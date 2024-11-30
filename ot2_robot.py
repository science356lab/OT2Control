'''
This file contains everything the server needs to run. It is seperate for organizational purposes
and because it must preserve compatibility between modern pandas 1.3 and deprecated .25 pandas
that the raspberry pi on the robot runs
The core is a class, the OT2Robot. This handles pipetting, communicating with the laptop,
and anything that involves the opentrons protocol API.
The OT2Robot uses Containers, and Labware
Container is a custom abstract class that has useful attributes for describing a single container
on the deck. e.g. loc, deck_pos, volume, height_calc, etc. see Container for more details
Labware is a custom abstract class that serves as a wrapper for opentrons labware objects, but
have more attributes, accessor methods, custom ways to pop wells, etc
This module also has the method for launching an eve server, launch_eve_server,
and if run directly from the command line, that function will be invoked.
'''

from abc import ABC
from abc import abstractmethod
from collections import defaultdict
from datetime import datetime
import pytz
import socket
import json
import dill
import math
import os
import shutil
import webbrowser
from tempfile import NamedTemporaryFile
import logging
import asyncio
import threading
import time
import traceback
import re

from bidict import bidict
import gspread
from df2gspread import df2gspread as d2g
from df2gspread import gspread2df as g2d
from oauth2client.service_account import ServiceAccountCredentials
import pandas as pd
import numpy as np
import opentrons.execute
from opentrons import protocol_api, simulate, types
from boltons.socketutils import BufferedSocket

from Armchair.armchair import Armchair
import Armchair.armchair as armchair
from df_utils import *
from exceptions import EmptyReagent

#CONTAINERS
class Container(ABC):
    """
    Abstract container class to be overwritten for well, tube, etc.  
    ABSTRACT ATTRIBUTES:  
        str name: the common name we use to refer to this container  
        float vol: the volume of the liquid in this container in uL  
        int deck_pos: the position on the deck  
        str loc: a location on the deck_pos object (e.g. 'A5')  
        Opentrons...Labware labware: an opentrons labware object for the deck_pos
        float conc: the concentration of the substance  
        float disp_height: the height to dispense at  
        float asp_height: the height to aspirate from  
        list<tup<timestamp, str, float> history: the history of this container. Contents:
          timestamp timestamp: the time of the addition/removal. Note that it may not be sorted
          str chem_name: the name of the chemical added or blank if aspiration
          float vol: the volume of chemical added/removed  
    CONSTANTS:  
        float DEAD_VOL: the volume at which this  
        float MIN_HEIGHT: the minimum height at which to pipette from   
    ABSTRACT METHODS:  
        _update_height void: updates self.height to height at which to pipet (a bit below water line)  
    IMPLEMENTED METHODS:  
        update_vol(float del_vol) void: updates the volume upon an aspiration  
        rewrite_history_first() void: esoteric method for rewriting the first entry of this
          container. useful for powders.  
        aspirate(float vol, Opentrons...pipette pipette, np.array<labware> lab_deck): 
          aspirates volume from this container.  
        dispense(float vol, Opentrons...pipette pipette, np.array<labware> lab_deck, float src): 
          dispenses volume from pipette into this container.  
        get_well(): returns the Opentrons well object associated with this container
        mix(Opentrons...pipette pipette, float mix_vol, int mix_code): mixes this container
    """

    def __init__(self, name, deck_pos, loc, labware, vol=0,  conc=1):
        self.name = name
        self.deck_pos = deck_pos
        self.loc = loc
        self.labware = labware
        self.vol = vol
        assert (self.vol < self.MAX_VOL), "tried to set volume of {} to {}uL, but {} has max capacity of {}uL".format(self.name, self.vol, self.name, self.MAX_VOL)
        self._update_height()
        self.conc = conc
        self.history = []
        if vol:
            #create an entry with yourself as first
            self.history.append((datetime.now(pytz.timezone('US/Pacific')).strftime('%d-%b-%Y %H:%M:%S:%f'), name, vol))

    DEAD_VOL = 0
    MIN_HEIGHT = 0

    @abstractmethod
    def _update_height(self):
        pass

    def update_vol(self, del_vol,name=''):
        '''
        params:  
            float del_vol: the change in volume. -vol is an aspiration  
            str name: the thing coming in if it is a dispense  
        Postconditions:
            the volume has been adjusted  
            height has been adjusted  
            the history has been updated  
        '''
        #if you are dispersing without specifying the name of incoming chemical, complain
        assert ((del_vol < 0) or (name and del_vol > 0)), 'Developer Error: dispensing without specifying src'
        self.history.append((datetime.now(pytz.timezone('US/Pacific')).strftime('%d-%b-%Y %H:%M:%S:%f'), name, del_vol))
        self.vol = self.vol + del_vol
        self._update_height()
        assert (self.vol < self.MAX_VOL + 1e-9), "tried to set volume of {} to {}uL, but {} has max capacity of {}uL".format(self.name, self.vol, self.name, self.MAX_VOL) #1e-9 is fudge

    def rewrite_history_first(self):
        '''
        This is a very niche method for now.  
        When creating a powder, you will want the first entry to correspond to the amount of 
          that reagent, rather than water, which is what you are physically transfering, so we
          reach past the beautiful abstaction and rewrite history.  
        Preconditions:  
            This chemicals name has been updated
        Postconditions:
            The first transfer in history is a transfer of this chemical into this well  
        '''
        self.history = [(self.history[0][0], self.name, self.history[0][2])]

    def aspirate(self, vol, pipette, lab_deck):
        '''
        params:  
            float vol: the volume to pipette in uL  
            Opentrons.pipette pipette: the pipette to use in the transfer  
            np.array<Labware> lab_deck: the indexed arrray of labware  
        raises:  
            EmptyReagent if don't have enough volume to pipette  
        Note:  
            it is the responsibility of the caller to update the pipette as dirty because
            this is a robot level attribute  
        Postconditions:  
            The pipette has aspirated vol from this container  
        '''
        #check to ensure you can pipette
        if self.aspiratible_vol < vol:
            #if you can't raise error to show that you are empty
            raise EmptyReagent('cannot aspirate {:.3}uL from {} because it only has {:.3}uL'.format(vol,self.name,float(self.aspiratible_vol)), self.name)
        #set aspiration height
        pipette.well_bottom_clearance.aspirate = self.asp_height
        #aspirate(well_obj)
        pipette.aspirate(vol, lab_deck[self.deck_pos].get_well(self.loc))
        #update the vol of src
        self.update_vol(-vol)
        #call cleanup
        self._aspirate_cleanup(pipette)

    def _aspirate_cleanup(self, pipette):
        '''
        This method is called at the end of an aspiration.
        It is used to do any end of aspiration cleanup like touching tip.  
        Implemented as a seperate method because it will likely be overridden
        for subclasses.
        params:  
            Opentrons.pipette pipette: the pipette to use in the transfer  
        '''
        pipette.touch_tip()
        #move tip *directly* to center of well/tube so it doesn't interact with the well/tube when it lifts up
        pipette.move_to(self.get_well().top(), force_direct=True)

    def dispense(self, vol, pipette, lab_deck, src):
        '''
        params:  
            float vol: the volume to pipette in uL  
            Opentrons.pipette pipette: the pipette to use in the transfer  
            np.array<Labware> lab_deck: the indexed arrray of labware  
            float src: the name of the reagent being put into this container
        Note:  
            it is the responsibility of the caller to update the pipette  
        Postconditions:  
            The pipette has aspirated vol from this container
        '''
        #set dispense height
        pipette.well_bottom_clearance.dispense = self.disp_height
        #dispense(well_obj)
        pipette.dispense(vol, lab_deck[self.deck_pos].get_well(self.loc))
        #update vol of dst
        self.update_vol(vol,src)
        #cleanup
        self._dispense_cleanup(pipette)

    def _dispense_cleanup(self, pipette):
        '''
        This method is called at the end of a dispense.
        It is used to do any end of dispense cleanup like touching tip.  
        Implemented as a seperate method because it will likely be overridden
        for subclasses.
        params:  
            Opentrons.pipette pipette: the pipette to use in the transfer  
        '''
        #blowout
        for i in range(4):
            pipette.blow_out()
        #wiggle - touch tip (spin fast inside well)
        pipette.touch_tip(radius=0.3,speed=40)

    def mix(self, pipette, mix_vol, mix_code):
        '''
        This method is used to mix the well. Part of the container because
        many of it's children will override this method to mix in a special way.  
        params:  
            Opentrons.pipette pipette: the piptette to use for the mix
            float mix_vol: the volume to mix with (this is almost always
              the volume of the pipette  
            int mix_code: integer code for what type of mix. This allows for
              different mix behaviors within a class, though the container
              just uses it for mix iterations, and many subclasses might
              choose to ignore it.  
        '''
        #set aspiration height
        pipette.well_bottom_clearance.aspirate = self.asp_height
        #set dispense height to same as asp
        pipette.well_bottom_clearance.dispense = self.asp_height
        #do the actual mix
        for i in range(2**mix_code):
            pipette.mix(1, mix_vol, self.get_well(), rate=100.0)
            pipette.blow_out()

    def get_well(self):
        '''
        returns Opentrons...Well: the well object this container is in
        '''
        return self.labware.wells_by_name()[self.loc]

    @property
    def disp_height(self):
        pass

    @property
    def asp_height(self):
        pass

    @property
    def aspiratible_vol(self):
        return self.vol - self.DEAD_VOL

    @property
    def MAX_VOL(self):
        return self.labware.wells_by_name()[self.loc]._geometry._max_volume

class MultiContainer(Container):
    '''
    In some cases, it is necessary to have multiple reagents of the same name.
    However, we maintain the assumption that you should only need to use one of 
    those reagents at a time.  
    The MultiContainer class is designed to meet this need. It takes as input an
    ordered list of Containers, and maintains that list as an attribute.  
    It also keeps a cont attribute that represents the current container being
    used. It will use that container until it runs out of volume at which point any
    call to aspirate will cause cont to be updated to the next Container in the
    list.  
    All inherited attributes, loc, vol,  etc. refer to the corresponding
    attributes of the current cont. With the EXCEPTION of aspirable_vol and history. aspirable_vol
    value corresponds to the sum of aspirable volumes of all of the containers
    in the list, and histoyr is the concatenated list of all of the containers.  
    Dispensing into a MultiContainer is a terrible idea. (which Container would
    you dispense into?). This class is meant for multiple stock reagents
    (especially water). If you want to make a product name it something else.
    Therefore, the dispense method is overriden to raise a NotImplemented error  
    ATTRIBUTES:
        Container cont: the current container. all inherited attributes correspond to this
          object, excpet aspirable vol.  
        int _cont_i: index of current cont in cont_list
        list<Containers> cont_list: The list of containers this class wraps.  
        df history: the history of this MultiContainer. This is a property that runs on top of
          the histories of the container_list  
    INHERITED ATTRIBUTES:  
        str name, float vol, int deck_pos, str loc, float disp_height, float asp_height,
          Opentrons.Labware labware  
    OVERRIDDEN CONSTANTS:  
        float DEAD_VOL: the volume at which this container is considered empty  
        float MIN_HEIGHT: the minimum height a tip can go  
        NOTE these also correspond to the current cont, so they will change. They're not
          technically const, but user should not write them ever.  
    INHERITED METHODS:  
        _update_height void, update_vol(float del_vol) void,  
    '''
    def __init__(self,cont_list):
        self.cont_list = cont_list
        self._cont_i = 0
        self.cont = cont_list[self._cont_i]
        
    def aspirate(self, vol, pipette, lab_deck):
        '''
        params:  
            float vol: the volume to pipette in uL  
            Opentrons.pipette pipette: the pipette to use in the transfer  
            np.array<Labware> lab_deck: the indexed arrray of labware  
        raises:  
            EmptyReagent if don't have enough volume to pipette  
        Note:  
            it is the responsibility of the caller to update the pipette as dirty because
            this is a robot level attribute.  
            This method is also somewhat inefficient. It cyles the reagent if it doesn't
            have enough volume for this entire aspiration, even if there is some volume
            left. Alternatively, one could aspirate that volume, and then aspirate the
            difference from the next container, but this would cause two moves of pipette,
            and will likely not save much liquid. (especially because the most volume you
            can aspirate in one go is the volume of the pipette.)  
        Postconditions:  
            The pipette has aspirated vol from this container
        '''
        #check to ensure you can pipette
        while self.cont.aspiratible_vol < vol:
            #if you can't (not enough vol left)
            try:
                #try to just move to the next one in the list
                self._update_cont()
            except IndexError:
                #you ran out of reagents in the list
                raise EmptyReagent('cannot aspirate {:.3}uL from {} because it only has {:.3}uL'.format(vol,self.name,float(self.aspiratible_vol)), self.name)
        #set aspiration height
        pipette.well_bottom_clearance.aspirate = self.asp_height
        #aspirate(well_obj)
        pipette.aspirate(vol, lab_deck[self.deck_pos].get_well(self.loc))
        #update the vol of src
        self.update_vol(-vol)
        #call cleanup
        self._aspirate_cleanup(pipette)

    def _update_cont(self):
        '''
        this method is called when one reagent is out and the current cont
        needs to be updated to the next in the list  
        Postconditions:  
            _cont_i has been incremented
            cont has been updated to next in the list
        raises:  
            IndexError if the cont index is out of bounds
        '''
        self._cont_i += 1
        self.cont = self.cont_list[self._cont_i]

    def dispense(self, vol, pipette, lab_deck, src):
        '''
        This should never be called on a multicontainer. It exists for class
        compatability, but will raise an error if called.  
        params:  
            float vol: the volume to pipette in uL  
            Opentrons.pipette pipette: the pipette to use in the transfer  
            np.array<Labware> lab_deck: the indexed arrray of labware  
            float src: the name of the reagent being put into this container
        Note:  
            it is the responsibility of the caller to update the pipette  
        Postconditions:  
            The pipette has aspirated vol from this container
        '''
        raise NotImplemented("A dispense was called on {}, but {} is a multicontainer. It should not be dispensed into".format(self.name,self.name))

    @property
    def aspiratible_vol(self):
        return sum([container.aspiratible_vol for container in self.cont_list[self._cont_i:]])
    
    @property
    def history(self):
        hist = []
        for cont in self.cont_list:
            hist += cont.history
        return hist

    #properties using the current object
    #these are just wrappers to direct calls to the current container
    @property
    def name(self):
        return self.cont.name
    @property
    def deck_pos(self):
        return self.cont.deck_pos
    @property
    def loc(self):
        return self.cont.loc
    @property
    def labware(self):
        return self.cont.labware
    @property
    def vol(self):
        return self.cont.vol
    @property
    def conc(self):
        return self.cont.conc
    @property
    def disp_height(self):
        return self.cont.disp_height
    @property
    def asp_height(self):
        return self.cont.asp_height
    #methods
    @property
    def _update_height(self):
        return self.cont._update_height
    @property
    def update_vol(self):
        return self.cont.update_vol
    @property
    def _aspirate_cleanup(self):
        return self.cont._aspirate_cleanup
    @property
    def rewrite_history_first(self):
        return self.cont.rewrite_history_first
    #constants
    @property
    def MAX_VOL(self):
        return self.cont.MAX_VOL
    @property
    def DEAD_VOL(self):
        return self.cont.DEAD_VOL
    @property
    def MIN_HEIGHT(self):
        return self.cont.MIN_HEIGHT

class Tube(Container):
    '''
    This abstract class implements shared features of all the tubes. Right now
    this is just the mix method for 15000 and 50000. 2000 overrides this method
    anyways.
    '''
    def mix(self, pipette, mix_vol, mix_code):
        '''
        This method is used to mix the well. Part of the container because
        many of it's children will override this method to mix in a special way.  
        params:  
            Opentrons.pipette pipette: the piptette to use for the mix
            float mix_vol: the volume to mix with (this is almost always
              the volume of the pipette  
            int mix_code: integer code for what type of mix. This allows for
              different mix behaviors within a class, though the container
              just uses it for mix iterations, and many subclasses might
              choose to ignore it.  
        '''
        NUM_HEIGHTS = 4
        # create an array of heights with the first height just a little lower
        # than the surface
        # top height -4 is carefully tuned to get tip in liquid
        top_height = max(self.height - 8, self.MIN_HEIGHT) 
        # The next part assumes you use a 300 uL pipette
        # it could be implemented for 20uL, but realistically, you
        # probably won't mix a tube with a 20uL pipette
        assert (mix_vol > 20), "Trying to mix {} on tube with 20uL pipette".format(self.name)
        # it is important that tip doesn't submerge itself, hence 55mm max depth
        if (top_height - self.MIN_HEIGHT < 50):
            # this is normal case.
            bottom_height = self.MIN_HEIGHT
        else:
            # this is case where you need to change the height so you don't dip
            # too deep
            bottom_height = top_height - 50
            print("<<eve>> warning tube is too full to mix completely")
        heights = np.linspace(bottom_height, top_height, num=NUM_HEIGHTS)
        for height in heights:
            #set aspiration height
            pipette.well_bottom_clearance.aspirate = height
            #set dispense height to same as asp
            pipette.well_bottom_clearance.dispense = height
            #do the actual mix
            for i in range(2**mix_code):
                pipette.mix(1, mix_vol, self.get_well(), rate=100.0)
                pipette.blow_out()

class Tube15000uL(Tube):
    """
    Spcific tube with measurements taken to provide implementations of abstract methods  
    INHERITED ATTRIBUTES:  
        str name, float vol, int deck_pos, str loc, float disp_height, float asp_height,
          Opentrons.Labware labware  
    OVERRIDDEN CONSTANTS:  
        float DEAD_VOL: the volume at which this container is considered empty  
        float MIN_HEIGHT: the minimum height a tip can go  
    INHERITED METHODS:  
        _update_height void, update_vol(float del_vol) void,  
    """

    DEAD_VOL = 2000
    MIN_HEIGHT = 4

    def __init__(self, name, deck_pos, loc, labware, mass=6.9731, conc=1):
        '''
        mass is defaulted to the avg_mass so that there is nothing in the container
        '''
        density_water_25C = 0.9970479 # g/mL
        avg_tube_mass15 = 6.9731 # grams
        self.mass = mass - avg_tube_mass15 # N = 1 (in grams) 
        assert (self.mass >= -1e-9),'the mass you entered for {} is less than the mass of the tube it\'s in.'.format(name)
        vol = (self.mass / density_water_25C) * 1000 # converts mL to uL
        super().__init__(name, deck_pos, loc, labware, vol, conc)
       # 15mm diameter for 15 ml tube  -5: Five mL mark is 19 mm high for the base/noncylindrical protion of tube 

    def _update_height(self):
        diameter_15 = 14.0 # mm (V1 number = 14.4504)
        height_bottom_cylinder = 30.5  #mm
        height = ((self.vol - self.DEAD_VOL)/(math.pi*(diameter_15/2)**2))+height_bottom_cylinder
        self.height = height if height > height_bottom_cylinder else self.MIN_HEIGHT


    @property
    def asp_height(self):
        tip_depth = 5
        return self.height - tip_depth

    @property
    def disp_height(self):
        min_disp_height = 40 #mm above the bottom of the tube
        disp_height_above_liquid = 10 #mm above the liquid level
        return max(self.height + disp_height_above_liquid, min_disp_height)
            
class Tube50000uL(Tube):
    """
    Spcific tube with measurements taken to provide implementations of abstract methods  
    INHERITED ATTRIBUTES:  
        str name, float vol, int deck_pos, str loc, float disp_height, float asp_height,
          Opentrons.Labware labware  
    OVERRIDDEN CONSTANTS:  
        float DEAD_VOL: the volume at which this container is considered empty  
        float MIN_HEIGHT: the minimum height a tip can go  
    INHERITED METHODS:  
        _update_height void, update_vol(float del_vol) void,  
    """

    DEAD_VOL = 5000
    MIN_HEIGHT = 4

    def __init__(self, name, deck_pos, loc, labware, mass=13.3950, conc=1):
        density_water_25C = 0.9970479 # g/mL
        avg_tube_mass50 = 13.3950 # grams
        self.mass = mass - avg_tube_mass50 # N = 1 (in grams) 
        assert (self.mass >= -1e-9),'the mass you entered for {} is less than the mass of the tube it\'s in.'.format(name)
        vol = (self.mass / density_water_25C) * 1000 # converts mL to uL
        super().__init__(name, deck_pos, loc, labware, vol, conc)
       # 15mm diameter for 15 ml tube  -5: Five mL mark is 19 mm high for the base/noncylindrical protion of tube 
        
    def _update_height(self):
        diameter_50 = 26.50 # mm (V1 number = 26.7586)
        height_bottom_cylinder = 21 #mm
        height = ((self.vol - self.DEAD_VOL)/(math.pi*(diameter_50/2)**2)) + height_bottom_cylinder
        self.height = height if height > height_bottom_cylinder else self.MIN_HEIGHT

    @property
    def asp_height(self):
        tip_depth = 5
        return self.height - tip_depth
    
    @property
    def disp_height(self):
        min_disp_height = 30 #mm above the bottom of the tube
        disp_height_above_liquid = 10 #mm above the liquid level
        return max(self.height + disp_height_above_liquid, min_disp_height)

class Tube2000uL(Tube):
    """
    2000uL tube with measurements taken to provide implementations of abstract methods  
    INHERITED ATTRIBUTES:  
         str name, float vol, int deck_pos, str loc, float disp_height, float asp_height,
          Opentrons.Labware labware  
    OVERRIDDEN CONSTANTS:  
        float DEAD_VOL: the volume at which this container is considered empty  
        float MIN_HEIGHT: the minimum height a tip can go  
    INHERITED METHODS:  
        _update_height void, update_vol(float del_vol) void,  
    """

    DEAD_VOL = 250 #uL
    MIN_HEIGHT = 6

    def __init__(self, name, deck_pos, loc, labware, mass=1.4, conc=2):
        density_water_4C = 0.9998395 # g/mL
        avg_tube_mass2 =  1.4        # grams
        self.mass = mass - avg_tube_mass2 # N = 1 (in grams) 
        assert (self.mass >= -1e-9),'the mass you entered for {} is less than the mass of the tube it\'s in.'.format(name)
        vol = (self.mass / density_water_4C) * 1000 # converts mL to uL
        super().__init__(name, deck_pos, loc, labware, vol, conc)
           
    def _update_height(self):
        diameter_2 = 8.30 # mm
        height_bottom_cylinder = 10.5 #mm
        height = ((self.vol - self.DEAD_VOL)/(math.pi*(diameter_2/2)**2)) + height_bottom_cylinder
        self.height = height if height > height_bottom_cylinder else self.MIN_HEIGHT

    @property
    def asp_height(self):
        tip_depth = 6 # mm
        return self.height - tip_depth

    @property
    def disp_height(self):
        height_disp_cutoff = 32 #mm above the bottom of the tube
        min_disp_height = 40 #mm above the bottom of the tube
        disp_height_above_liquid = 7 #mm above the liquid level
        return self.height + disp_height_above_liquid if self.height > height_disp_cutoff else min_disp_height

    def mix(self, pipette, mix_vol, mix_code):
        '''
        This method is used to mix the well. Part of the container because
        many of it's children will override this method to mix in a special way.  
        params:  
            Opentrons.pipette pipette: the piptette to use for the mix
            float mix_vol: the volume to mix with (this is almost always
              the volume of the pipette  
            int mix_code: integer code for what type of mix. This allows for
              different mix behaviors within a class, though the container
              just uses it for mix iterations, and many subclasses might
              choose to ignore it.  
        '''
        #create an array of heights with the first height just a little lower than the surface
        heights = np.linspace(self.MIN_HEIGHT, self.asp_height, 3)
        for height in heights:
            #set aspiration height
            pipette.well_bottom_clearance.aspirate = height
            #set dispense height to same as asp
            pipette.well_bottom_clearance.dispense = height
            #do the actual mix
            for i in range(2**mix_code):
                pipette.mix(1, mix_vol, self.get_well(), rate=100.0)
                pipette.blow_out()

class Well(Container, ABC):
    """
    Abstract class for a well96
    INHERITED ATTRIBUTES:  
        str name, float vol, int deck_pos, str loc, float disp_height, float asp_height,
          Opentrons.Labware labware  
    INHERITED CONSTANTS:  
        float DEAD_VOL: the volume at which this container is considered empty  
    OVERRIDDEN CONSTANTS:  
        float MIN_HEIGHT: the minimum height a tip can go  
    INHERITED METHODS:  
        _update_height void, update_vol(float del_vol) void,  
    """
    MIN_HEIGHT = 1

    def __init__(self, name, deck_pos, loc, labware, vol=0, conc=1):
        #vol is defaulted here because the well will probably start without anything in it
        super().__init__(name, deck_pos, loc, labware, vol, conc)
           
    def _update_height(self):
        #this method is not needed for a well of such small size because we always aspirate
        #and dispense at the same heights
        self.height = None

    @property
    @abstractmethod
    def disp_height(self):
        pass

    @property
    def asp_height(self):
        return self.MIN_HEIGHT

class Well96(Well):
    """
    a well in a 96 well plate  
    INHERITED ATTRIBUTES:  
        str name, float vol, int deck_pos, str loc, float disp_height, float asp_height,
          Opentrons.Labware labware  
    INHERITED CONSTANTS:  
        float MIN_HEIGHT: the minimum height a tip can go  
    OVERRIDDEN CONSTANTS:  
        float DEAD_VOL: the volume at which this container is considered empty  
    INHERITED METHODS:  
        _update_height void, update_vol(float del_vol) void,  
    """
    DEAD_VOL = 40 #uL

    @property
    def disp_height(self):
        return 9 #mm

class Well24(Well):
    '''
    a well in a 24 well plate
    INHERITED ATTRIBUTES:  
        str name, float vol, int deck_pos, str loc, float disp_height, float asp_height,
          Opentrons.Labware labware  
    INHERITED CONSTANTS:  
        float MIN_HEIGHT: the minimum height a tip can go  
    OVERRIDDEN CONSTANTS:  
        float DEAD_VOL: the volume at which this container is considered empty  
    INHERITED METHODS:  
        _update_height void, update_vol(float del_vol) void,  
    '''
    DEAD_VOL = 400 #uL

    @property
    def disp_height(self):
        return 18 #mm

#LABWARE
class Labware(ABC):
    '''
    The opentrons labware class is lacking in some regards. It does not appear to have
    a method for removing tubes from the labware, which is what I need to do, hence this
    wrapper class to hold opentrons labware objects
    Note that tipracks are not included. The way we access them is normal enough that opentrons
    API does everything we need for them  
    ATTRIBUTES:  
        Opentrons.Labware labware: the opentrons object  
        bool full: True if there are no more empty containers  
        int deck_pos: to map back to deck position  
        str name: the name associated with this labware  
    CONSTANTS:  
        list<str> CONTAINERS_SERVICED: the container types on this labware  
    ABSTRACT METHODS:  
        get_container_type(loc) str: returns the type of container at that location  
        pop_next_well(vol=None) str: returns the index of the next available well
          If there are no available wells of the volume requested, return None  
    '''

    CONTAINERS_SERVICED = []

    def __init__(self, labware, deck_pos):
        self.labware = labware
        self.full = False
        self.deck_pos = deck_pos

    @abstractmethod
    def pop_next_well(self, vol=None, container_type=None):
        '''
        returns the next available well
        Or returns None if there is no next availible well with specified volume
        container_type takes precedence over volume, but you shouldn't need to call it with both
        '''
        pass

    @abstractmethod
    def get_container_type(self, loc):
        '''
        params:  
            str loc: the location on the labware. e.g. A1  
        returns:  
            str the type of container class  
        '''
        pass

    def get_well(self,loc):
        '''
        params:  
            str loc: the location on the labaware e.g. A1  
        returns:  
            the opentrons well object at that location  
        '''
        return self.labware.wells_by_name()[loc]

    @property
    def name(self):
        return self.labware.name

class TubeHolder(Labware):
    '''
    Subclass of Labware object that may not have all containers filled, and allows for diff
    sized containers  
    INHERITED METHODS:
        pop_next_well(vol=None) str: Note vol is should be provided here, otherwise a random size
          will be chosen  
        get_container_type(loc) str  
    INHERITED_ATTRIBUTES:
        Opentrons.Labware labware, bool full, int deck_pos, str name  
    OVERRIDEN CONSTANTS
        list<str> CONTAINERS_SERVICED  
    ATTRIBUTES:
        list<str> empty_tubes: contains locs of the empty tubes. Necessary because the user may
          not put tubes into every slot. Sorted order smallest tube to largest  
    '''

    CONTAINERS_SERVICED = ['Tube50000uL', 'Tube15000uL', 'Tube2000uL']

    def __init__(self, labware, empty_tubes, deck_pos):
        super().__init__(labware,deck_pos)
        #We create a dictionary of tubes with the container as the key and a list as the 
        #value. The list contains all tubes that fit that volume range
        self.empty_tubes={tube_type:[] for tube_type in self.CONTAINERS_SERVICED}
        for tube in empty_tubes:
            self.empty_tubes[self.get_container_type(tube)].append(tube)
        self.full = not self.empty_tubes


    def pop_next_well(self, vol=None, container_type=None):
        '''
        Gets the next available tube. If vol is specified, will return an
        appropriately sized tube. Otherwise it will return a tube. It makes no guarentees that
        tube will be the correct size. It is not recommended this method be called without
        a volume argument  
        params:  
            float vol: used to determine an appropriate sized tube  
            str container_type: the type of container requested  
        returns:  
            str: loc the location of the smallest next tube that can accomodate the volume  
            None: if it can't be accomodated  
        '''
        if not self.full:
            if container_type:
                #here I'm assuming you wouldn't want to put more volume in a tube than it can fit
                viable_tubes = self.empty_tubes[container_type]
            elif vol:
                #neat trick
                viable_tubes = self.empty_tubes[self.get_container_type(vol=vol)]
                if not viable_tubes:
                    #but if it didn't work you need to check everything
                    for tube_type in self.CONTAINERS_SERVICED:
                        viable_tubes = self.empty_tubes[tube_type]
                        if viable_tubes:
                            #check if the volume is still ok
                            capacity = self.labware.wells_by_name()[viable_tubes[0]]._geometry._max_volume
                            if vol < capacity:
                                break
            else:
                #volume was not specified
                #return the next smallest tube.
                #this always returns because you aren't empty
                for tube_type in self.CONTAINERS_SERVICED:
                    if self.empty_tubes[tube_type]:
                        viable_tubes = self.empty_tubes[tube_type]
                        break
            if viable_tubes:
                tube_loc = viable_tubes.pop()
                self.update_full()
                return tube_loc
            else:
                return None
        else:
            #self.empty_tubes is empty!
            return None

    def update_full(self):
        '''
        updates self.full
        '''
        self.full=True
        for tube_type in self.CONTAINERS_SERVICED:
            if self.empty_tubes[tube_type]:
                self.full = False
                return
        
    def get_container_type(self, loc=None, vol=None):
        '''
        NOTE internally, this method is a little different, but the user should use as 
        outlined below
        returns type of container  
        params:  
            str loc: the location on this labware  
        returns:  
            str: the type of container at that loc  
        '''
        if not vol:
            tube_capacity = self.labware.wells_by_name()[loc]._geometry._max_volume
        else:
            tube_capacity = vol
        if tube_capacity <= 2000:
            return 'Tube2000uL'
        elif tube_capacity <= 15000:
            return 'Tube15000uL'
        else:
            return 'Tube50000uL'


class WellPlate(Labware):
    '''
    subclass of labware for dealing with plates  
    INHERITED METHODS:  
        pop_next_well(vol=None,container_type=None) str: vol should be provided to 
          check if well is big enough. container_type is for compatibility  
        get_container_type(loc) str  
    INHERITED_ATTRIBUTES:  
        Opentrons.Labware labware, bool full, int deck_pos, str name  
    ATTRIBUTES:  
        int current_well: the well number your on (NOT loc!)  
    '''

    def __init__(self, labware, first_well, deck_pos):
        super().__init__(labware, deck_pos)
        #allow for none initialization
        all_wells = labware.wells()
        self.current_well = 0
        while self.current_well < len(all_wells) and all_wells[self.current_well]._impl._name != first_well:
            self.current_well += 1
        #if you overflowed you'll be correted here
        self.full = self.current_well >= len(labware.wells())

    def pop_next_well(self, vol=None,container_type=None):
        '''
        returns the next well if there is one, otherwise returns None  
        params:  
            float vol: used to determine if your reaction can be fit in a well  
            str container_type: should never be used. Here for compatibility  
        returns:  
            str: the well loc if it can accomadate the request  
            None: if can't accomodate request  
        '''
        if not self.full:
            well = self.labware.wells()[self.current_well] 
            capacity = well._geometry._max_volume
            if capacity > vol:
                #have a well that works
                self.current_well += 1
                self.full = self.current_well >= len(self.labware.wells())
                return well._impl._name
            else:
                #requested volume is too large
                return None
        else:
            #don't have any more room
            return None
    

class WellPlate96(WellPlate):
    '''
    subclass of WellPlate for 96 well plates
    INHERITED METHODS:  
        pop_next_well(vol=None,container_type=None) str: vol should be provided to 
          check if well is big enough. container_type is for compatibility  
        get_container_type(loc) str  
    INHERITED_ATTRIBUTES:  
        Opentrons.Labware labware, bool full, int deck_pos, str name  
    ATTRIBUTES:  
        int current_well: the well number your on (NOT loc!)  
    OVERRIDEN CONSTANTS:  
        list<str> CONTAINERS_SERVICED  
    OVERRIDEN METHODS:
        get_container_type
    '''

    CONTAINERS_SERVICED = ['Well96']

    def get_container_type(self, loc):
        '''
        params:  
            str loc: loc on the labware  
        returns:  
            str: the type of container  
        '''
        return 'Well96'

class WellPlate24(WellPlate):
    '''
    subclass of WellPlate for 24 well plates
    INHERITED METHODS:  
        pop_next_well(vol=None,container_type=None) str: vol should be provided to 
          check if well is big enough. container_type is for compatibility  
        get_container_type(loc) str  
    INHERITED_ATTRIBUTES:  
        Opentrons.Labware labware, bool full, int deck_pos, str name  
    ATTRIBUTES:  
        int current_well: the well number your on (NOT loc!)  
    OVERRIDEN CONSTANTS:  
        list<str> CONTAINERS_SERVICED  
    OVERRIDEN METHODS:
        get_container_type
    '''

    CONTAINERS_SERVICED = ['Well24']

    def get_container_type(self, loc):
        '''
        params:  
            str loc: loc on the labware  
        returns:  
            str: the type of container  
        '''
        return 'Well24'

#Robot
class OT2Robot():
    """
    This class is responsible for controlling the robot from the Raspberry Pi.   
    ATTRIBUTES:  
        Dict<str, Container> containers: maps from a common name to a Container object  
        Dict<str:Dict<str:Obj>> pipettes: JSON style dict. First key is the arm_pos 
          second is the attribute  
            'size' float: the size of this pipette in uL  
            'last_used' str: the chem_name of the last chemical used. 'clean' is used to denote a
              clean pipette  
        str my_ip: IPv4 LAN address of this machine  
        Armchair.Armchair portal: the portal connected to the controller  
        str controller_ip: the ip of the controller  
        bool simulate: true if this protocol is being simulated. (different from the simulate in
          the protocol. This is about whether we want to execute pauses.  
        np.array<Labware> lab_deck: shape (12,) custom labware objects indexed by their
          locations on the deck. (so lab_deck[0] is not used and we live with that)  
        Opentrons...ProtocolContext protocol: the protocol object of this session  
        str root_p: the path to the root output  
        str debug_p: the path for debuging  
        str logs_p: the path to the log outputs  
        dict<str:tuple<Container,float>> dry_containers: maps container name to a container
          object and a volume of water needed to turn it into a reagent  
        dict<str:func> exec_funcs: a registry that holds all of the functions that respond to
          an armchair request mapped by their armchair command_type  
        opentrons.temp_module temp_module: the opentrons object for temperature controller  
    METHODS:  
        execute(command_type, cid, arguments) int: Takes in the recieved output of an Armchair
          recv_pack, and executes the command. Will usually send a ready (except for GHOST type)
          Returns 1 in normal situation if active. Returns 0 for closing  
        dump_well_map() void: writes a wellmap to the wellmap.tsv  
        dump_well_histories() void: writes the histories of each well to well_history.tsv  
    """

    #Don't try to read this. Use an online json formatter 
    _LABWARE_TYPES = { "96_well_plate": { "opentrons_name": "corning_96_wellplate_360ul_flat", "groups": [ "well_plate","WellPlate96" ], 'definition_path': "" }, "24_well_plate": { "opentrons_name": "corning_24_wellplate_3.4ml_flat", "groups": [ "well_plate", "WellPlate24" ], 'definition_path': "" }, "48_well_plate": { "opentrons_name": "corning_48_wellplate_1.6ml_flat", "groups": [ "well_plate", "WellPlate48" ], 'definition_path': "" }, "tip_rack_20uL": { "opentrons_name": "opentrons_96_tiprack_20ul", "groups": [ "tip_rack" ], 'definition_path': "" }, "tip_rack_300uL": { "opentrons_name": "opentrons_96_tiprack_300ul", "groups": [ "tip_rack" ], 'definition_path': "" }, "tip_rack_1000uL": { "opentrons_name": "opentrons_96_tiprack_1000ul", "groups": [ "tip_rack" ], 'definition_path': "" }, "tube_holder_10": { "opentrons_name": "opentrons_10_tuberack_falcon_4x50ml_6x15ml_conical", "groups": [ "tube_holder" ], 'definition_path': "" }, "temp_mod_24_tube": { "opentrons_name": "opentrons_24_aluminumblock_generic_2ml_screwcap", "groups": [ "tube_holder", "temp_mod" ], 'definition_path': "" }, "platereader4": { "opentrons_name": "plate_reader_4", "groups": [ "well_plate", "WellPlate96", "platereader" ], "definition_path": "LabwareDefs/plate_reader_4.json" }, "platereader7": { "opentrons_name": "plate_reader_7", "groups": [ "well_plate", "WellPlate96", "platereader" ], "definition_path": "LabwareDefs/plate_reader_7.json" }, "platereader": { "opentrons_name": "", "groups": [ "well_plate", "WellPlate96", "platereader" ] } }
    _PIPETTE_TYPES = {"300uL_pipette":{"opentrons_name":"p300_single_gen2"},"1000uL_pipette":{"opentrons_name":"p1000_single_gen2"},"20uL_pipette":{"opentrons_name":"p20_single_gen2"}}

    exec_funcs = {} #a dictionary mapping armchair commands to their appropriate handler func

    def exec_func(name, exit_code, send_ready, exec_funcs):
        '''
        register decorator for exec_funcs  
        params:  
            str name: the name of the armchair command for which to invoke this func  
            int exit_code: the code this should return on exit  
            bool send_ready: if true, will send a ready command  
            dict exec_funcs: the dictionary of armchair handler funcs  
        returns:  
            function: the unmodified function you're decorating  
        Postconditions:  
            exec_funcs has had a function appended to it with that is the same as the decorated
            function, but it has a new keyword argument, cid, and it sends a ready pack before it
            returns if you specified send_ready=True
        '''
        #return the func without the ready and exit code stuff in case you want to reuse it
        #somewhere else
        def echo_func(func):
            #register a version of the function that sends ready if needed and has exit code
            @functools.wraps(func)
            def decorated(*args, **kwargs):
                self = args[0]
                kwargs_copy = kwargs.copy()
                del(kwargs_copy['cid'])
                func(self,*args[1:],**kwargs_copy)
                if send_ready:
                    self.portal.send_pack('ready',kwargs['cid'])
                return exit_code
            exec_funcs[name] = decorated
            #finally just echo the func
            return func
        return echo_func

    def __init__(self, simulate, using_temp_ctrl, temp, labware_df, instruments, reagent_df, my_ip, controller_ip, portal, dry_containers_df):
        '''
        params:  
            bool simulate: if true, the robot will run in simulation mode only  
            bool using_temp_ctrl: true if you want to use the temperature control module  
            float temp: the temperature to keep the control module at.  
            df labware_df:  
                + str name: the common name of the labware  
                + str first_usable: the first tip/well to use  
                + int deck_pos: the position on the deck of this labware  
                + str empty_list: the available slots for empty tubes format 'A1,B2,...' No specific
                  order  
            Dict<str:str> instruments: keys are ['left', 'right'] corresponding to arm slots. vals
              are the pipette names filled in  
            df reagent_df: info on reagents. columns from sheet. See excel specification  
            str my_ip: the IP address of the robot  
            str controller_ip: the IP address of the controller  
            Armchair.Armchair portal: the Armchair object connected to the controller  
            df dry_containers:
                + float conc: concentration desired when finished
                + str loc: location on labware
                + int deck_pos: the location on deck
                + float required_vol: the volume of water needed to create the solution
        postconditions:  
            protocol has been initialzied  
            containers and tip_racks have been created  
            labware has been initialized  
            CAUTION: the values of tip_racks and containers must be sent from the client.
              it is the client's responsibility to make sure that these are initialized prior
              to operating with them  
        '''
        self._load_calibrations()
        #convert args back to df
        labware_df = pd.DataFrame(labware_df)
        #index of reagent_df needs to be set because it can have multiple chemicals of same
        #name, in which case it doesn't reduce nicely to a dict
        reagent_df = pd.DataFrame(reagent_df).set_index('index')
        dry_containers_df = pd.DataFrame(dry_containers_df).set_index('index')
        self.containers = {}
        self.pipettes = {}
        self.temp_module = None #will be overwritten if used
        self.my_ip = my_ip
        self.portal = portal
        self.controller_ip = controller_ip
        self.simulate = simulate

        #like protocol.deck, but with custom labware wrappers
        self.lab_deck = np.full(12, None, dtype='object') #note first slot not used

        if simulate:
            # define version number and define protocol object
            self.protocol = opentrons.simulate.get_protocol_api('2.12')
        else:
            self.protocol = opentrons.execute.get_protocol_api('2.12')
            self.protocol.set_rail_lights(on = True)
            self.protocol.rail_lights_on 
        self.protocol.home() # Homes the pipette tip
        #empty list was in comma sep form for easy shipping. unpack now to list
        labware_df['empty_list'] = labware_df['empty_list'].apply(lambda x: x.split(',')
                if x else [])
        self._init_params()
        self._init_directories()
        self._init_labware(labware_df, using_temp_ctrl, temp)
        self._init_dry_containers(dry_containers_df)
        self._init_instruments(instruments, labware_df)
        self._init_reagents(reagent_df)

    def _load_calibrations(self):
        '''
        Loads in the calibrations file
        '''
        with open("calibrations.json", 'r') as file:
            self._CALIBRATIONS = json.load(file)

    def _init_directories(self):
        '''
        The debug/directory structure of the robot is not intended to be stored for long periods
        of time. This is becuase the files should be shipped over FTP to laptop. In the event
        of an epic fail, e.g. where network went down and has no means to FTP back to laptop  
        Postconditions: the following directory structure has been contstructed
            Eve_Out: root  
                Debug: populated with error information. Used on crash  
                Logs: log files for eve  
        '''
        #clean up last time
        if os.path.exists('Eve_Out'):
            shutil.rmtree('Eve_Out')
        #make new folders
        os.mkdir('Eve_Out')
        os.mkdir('Eve_Out/Debug')
        os.mkdir('Eve_Out/Logs')
        self.root_p = 'Eve_Out/'
        self.debug_p = os.path.join(self.root_p, 'Debug')
        self.logs_p = os.path.join(self.root_p, 'Logs')

    def _init_dry_containers(self, dry_containers_df):
        '''
        initializes self._dry_containers. This method should only be run during init. It's 
        a little odd because it initializes containers to locations on the lab deck without
        any comunication to those labware objects. This gives a lot of power to the user.
        Please don't double book or make up locations on the labware  
        params:  
            df dry_containers_df: as recieved by init  
        Postconditions:  
            dry_containers have been initialized internally.  
            Some notes about dry_containers here.  
            + keys are chemical names WITHOUT C<conc>  
            + vals are lists of tuples<Container, float, float> correspoding to the container
              it's in, the mass of the powder W/O CONTAINER, and the molar mass  
        '''
        #indices don't align for apply if empty so must check
        if not dry_containers_df.empty:
            #initialize containers in case of duplicates
            self.dry_containers = {name:[] for name in dry_containers_df.index.unique()}
            dry_containers_df['container_types'] = dry_containers_df[['deck_pos','loc']\
                    ].apply(lambda row: self.lab_deck[row['deck_pos']].get_container_type(\
                    row['loc']),axis=1)
            for name, loc, deck_pos, mass, molar_mass, container_type in \
                    dry_containers_df.itertuples():
                self.dry_containers[name].append((self._construct_container(container_type, \
                        name, deck_pos,loc), mass, molar_mass))
        else:
            self.dry_containers = {}

    def _init_reagents(self, reagent_df):
        '''
        params:  
            df reagent_df: as passed to init  
        Postconditions:
            the dictionary, self.containers, has been initialized to have name keys to container
              objects  
        '''
        reagent_df['container_types'] = reagent_df[['deck_pos','loc']].apply(lambda row: 
                self.lab_deck[row['deck_pos']].get_container_type(row['loc']),axis=1)
        for name in reagent_df.index.unique():
            chem_info = reagent_df.loc[name]
            if isinstance(chem_info, pd.DataFrame):
                #multiple instances with the same name, so must create multicontainers
                self.containers[name] = self._construct_multicontainer(chem_info)
            else:
                #only one container with name. In this case is a series
                self.containers[name] = self._construct_container(
                        chem_info['container_types'], name, chem_info['deck_pos'],
                        chem_info['loc'], mass=chem_info['mass'], conc=chem_info['conc'])

    def _construct_multicontainer(self, chem_info):
        '''
        params:  
            df chem_info: dataframe of structure of reagent_df, but has a single chemical name
              for all indices  
        returns:  
            MultiContainer: a Container with all of the reagents in its cont_list  
        '''
        cont_list = [
            self._construct_container(container_type, name, deck_pos,loc, mass=mass, conc=conc)
            for name, conc, loc, deck_pos, mass, container_type in chem_info.itertuples()
            ]
        return MultiContainer(cont_list)

    def _construct_container(self, container_type, name, deck_pos, loc, **kwargs):
        '''
        params:  
            str container_type: the type of container you want to instantiate  
            str name: the chemical name  
            int deck_pos: labware position on deck  
            str loc: the location on the labware  
          **kwargs:  
            + float mass: the mass of the starting contents  
            + float conc: the concentration of the starting components  
        returns:  
            Container: a container object of the type you specified  
        '''
        labware = self.lab_deck[deck_pos].labware
        if container_type == 'Tube2000uL':
            return Tube2000uL(name, deck_pos, loc, labware, **kwargs)
        elif container_type == 'Tube15000uL':
            return Tube15000uL(name, deck_pos, loc, labware, **kwargs)
        elif container_type == 'Tube50000uL':
            return Tube50000uL(name, deck_pos, loc, labware, **kwargs)
        elif container_type == 'Well96':
            #Note we don't yet have a way to specify volume since we assumed that we would
            #always be weighing in the input template. Future feature allows volume to be
            #specified in sheets making this last step more interesting
            return Well96(name, deck_pos, loc, labware, **kwargs)
        elif container_type == 'Well24':
            return Well24(name, deck_pos, loc, labware, **kwargs)
        else:
            raise Exception('Invalid container type')
       
    def _init_params(self):
        '''
        Set speed to something we like
        '''
        self.protocol.max_speeds['X'] = 250
        self.protocol.max_speeds['Y'] = 250

    def _init_temp_mod(self, name, using_temp_ctrl, temp, deck_pos, empty_tubes):
        '''
        initializes the temperature module  
        params:  
            str name: the common name of the labware  
            bool using_temp_ctrl: true if using temperature control  
            float temp: the temperature you want it at  
            int deck_pos: the deck_position of the temperature module  
            list<tup<str, float>> empty_tubes: the empty_tubes associated with this tube holder
              the tuple holds the name of the tube and the volume associated with it  
        Postconditions:
            the temperature module has been initialized  
            the labware wrapper for these tubes has been initialized and added to the deck  
            self.temp_module is the opentrols object for the temperature module  
        '''
        if using_temp_ctrl:
            self.temp_module = self.protocol.load_module('temperature module gen2', 3)
            self.temp_module.set_temperature(temp)
            opentrons_name = self._LABWARE_TYPES[name]['opentrons_name']
            labware = self.temp_module.load_labware(opentrons_name,label=name)
            #this will always be a tube holder
            self._add_to_deck(name, deck_pos, labware, empty_containers=empty_tubes)
            assert( temp >= 4 and temp <= 95), "invalid temperature defined"
    

        
    def _init_custom_labware(self, name, deck_pos, **kwargs):
        '''
        initializes custom built labware by reading from json
        initializes the labware_deck  
        params:  
            str name: the common name of the labware  
            str deck_pos: the position on the deck for the labware  
        kwargs:
            + NOTE this is really here for compatibility since it's just one keyword that should  
            always be passed. It's here in case we decide to use other types of labware in the  
            future
            + str first_well: the first available well in the labware  
        '''
        with open(self._LABWARE_TYPES[name]['definition_path'], 'r') as labware_def_file:
            labware_def = json.load(labware_def_file)
        labware = self.protocol.load_labware_from_definition(labware_def, deck_pos,label=name)
        self._add_to_deck(name, deck_pos, labware, **kwargs)

    def _add_to_deck(self, name, deck_pos, labware, **kwargs):
        '''
        constructs the appropriate labware object  
        params:  
            str name: the common name for the labware  
            int deck_pos: the deck position of the labware object  
            Opentrons.labware: labware  
            kwargs:  
                + list empty_containers<str>: the list of the empty locations on the labware  
                + str first_well: the first available well in the labware  
        Postconditions:
            an entry has been added to the lab_deck  
        '''
        groups = self._LABWARE_TYPES[name]['groups']
        if 'tube_holder' in groups:
            self.lab_deck[deck_pos] = TubeHolder(labware, kwargs['empty_containers'], deck_pos)
        elif 'WellPlate96' in groups:
            self.lab_deck[deck_pos] = WellPlate96(labware, kwargs['first_well'], deck_pos)
        elif 'WellPlate24' in groups:
            self.lab_deck[deck_pos] = WellPlate24(labware, kwargs['first_well'], deck_pos)
        else:
            raise Exception("Sorry, Illegal Labware Option, {}. {} is not a tube or plate".format(name,name))
        #after you've added the labware, you must calibrate
        #offset is a dictionary with keys, x,y,z and float offset vals
        offset = self._CALIBRATIONS[self._LABWARE_TYPES[name]['opentrons_name']]
        labware.set_offset(**offset)

    def _init_labware(self, labware_df, using_temp_ctrl, temp):
        '''
        initializes the labware objects in the protocol and pipettes.
        params:  
            df labware_df: as recieved in __init__  
        Postconditions:
            The deck has been initialized with labware  
        '''
        for deck_pos, name, first_usable, empty_list in labware_df.itertuples(index=False):
            #diff types of labware need diff initializations
            if self._LABWARE_TYPES[name]['definition_path']:
                #plate readers (or other custom?)
                self._init_custom_labware(name, deck_pos, first_well=first_usable)
            elif 'temp_mod' in self._LABWARE_TYPES[name]['groups']:
                #temperature controlled racks
                self._init_temp_mod(name, using_temp_ctrl, 
                        temp, deck_pos, empty_tubes=empty_list)
            else:
                #everything else
                opentrons_name = self._LABWARE_TYPES[name]['opentrons_name']
                labware = self.protocol.load_labware(opentrons_name,deck_pos,label=name)
                if 'well_plate' in self._LABWARE_TYPES[name]['groups']:
                    self._add_to_deck(name, deck_pos, labware, first_well=first_usable)
                elif 'tube_holder' in self._LABWARE_TYPES[name]['groups']:
                    self._add_to_deck(name, deck_pos, labware, empty_containers=empty_list)
                #if it's none of the above, it's a tip rack. We don't need them on the deck

        
    def _init_instruments(self,instruments, labware_df):
        '''
        initializes the opentrons instruments (pipettes) and sets first tips for pipettes  
        params:  
            Dict<str:str> instruments: as recieved in __init__  
            df labware_df: as recieved in __init__  
        Postconditions:
            the pipettes have been initialized and   
            tip racks have been given first tips  
        '''
        for arm_pos, pipette_name in instruments.items():
            #lookup opentrons name
            opentrons_name = self._PIPETTE_TYPES[pipette_name]['opentrons_name']
            #get the size of this pipette
            pipette_size = pipette_name[:pipette_name.find('uL')]
            #get the row inds for which the size is the same
            tip_row_inds = labware_df['name'].apply(lambda name: 
                'tip_rack' in self._LABWARE_TYPES[name]['groups'] and pipette_size == 
                name[name.rfind('_')+1:name.rfind('uL')])
            tip_rows = labware_df.loc[tip_row_inds]
            #get the opentrons tip rack objects corresponding to the deck positions that
            #have tip racks
            tip_racks = [self.protocol.loaded_labwares[deck_pos] for deck_pos in tip_rows['deck_pos']]
            #load the pipette
            pipette = self.protocol.load_instrument(opentrons_name,arm_pos,tip_racks=tip_racks)
            #get the row with the largest lexographic starting tip e.g. (B1 > A0)
            #and then get the deck position
            #this is the tip rack that has used tips
            used_rack_row = tip_rows.loc[self._lexo_argmax(tip_rows['first_usable'])]
            #get opentrons object
            used_rack = self.protocol.loaded_labwares[used_rack_row['deck_pos']]
            #set starting tip
            pipette.starting_tip = used_rack.well(used_rack_row['first_usable'])
            pipette.pick_up_tip()
            #update self.pipettes
            self.pipettes[arm_pos] = {'size':float(pipette_size),'last_used':'clean','pipette':pipette}
            print("init info:")
            print(self.pipettes[arm_pos])
            print(self.pipettes[arm_pos]['pipette'].tip_racks)
        return

    def _lexo_argmax(self, s):
        '''
        pandas does not have a lexographic idxmax, so I have supplied one  
        Params:
            pd.Series s: a series of strings to be compared lexographically  
        returns:  
            Object: the pandas index associated with that string  
        '''
        max_str = ''
        max_idx = None
        for i, val in s.iteritems():
            max_str = max(max_str, val)
            max_idx = i
        return i
 
    @exec_func('init_containers', 1, True, exec_funcs)
    def _exec_init_containers(self, product_df):
        '''
        used to initialize empty containers, which is useful before transfer steps to new chemicals
        especially if we have preferences for where those chemicals are put  
        Params:
            df product_df: as generated in client init_robot  
        Postconditions:
            every container has been initialized according to the parameters specified  
        '''
        product_df = pd.DataFrame(product_df)
        for chem_name, req_labware, req_container, max_vol in product_df.itertuples():
            container = None
            #if you've already initialized this complane
            if chem_name in self.containers:
                raise Exception("you tried to initialize {},\
                        but there is already an entry for {}".format(chem_name, chem_name))
            #filter labware
            viable_labware =[]
            for viable in self.lab_deck:
                if viable:
                    labware_ok = not req_labware or (viable.name == req_labware or \
                            req_labware in self._LABWARE_TYPES[viable.name]['groups'])
                            #last bit necessary for platereader-> platereader4/platereader7
                    container_ok = not req_container or (req_container in viable.CONTAINERS_SERVICED)
                    if labware_ok and container_ok:
                        viable_labware.append(viable)
            #sort the list so that platreader slots are prefered
            viable_labware.sort(key=lambda x: self._exec_init_containers.priority[x.name])
            #iterate through the filtered labware and pick the first one that 
            loc, deck_pos, container_type  = None, None, None
            i = 0
            while not loc:
                try:
                    viable = viable_labware[i]
                except IndexError: 
                    message = 'No containers to put {} with labware type {} and container type \
                            {} with maximum volume {}.'.format(chem_name, \
                            req_labware, req_container, max_vol) 
                    raise Exception(message)
                next_container_loc = viable.pop_next_well(vol=max_vol,container_type=req_container)
                if next_container_loc:
                    #that piece of labware has space for you
                    loc = next_container_loc
                    deck_pos = viable.deck_pos
                    container_type = viable.get_container_type(loc)
                i += 1
            self.containers[chem_name] = self._construct_container(container_type, 
                    chem_name, deck_pos, loc)

    def _get_conc(self, chem_name):
        '''
        handy method for getting the concentration from a chemical name  
        params:  
            str chem_name: the chemical name to strip a concentration from  
        returns:  
            float: the concentration parsed from the chem_name  
        '''
        return float(re.search('C\d*\.\d*$', chem_name).group(0)[1:])

    def _get_reagent(self, chem_name):
        '''
        handy method for getting the reagent from a chemical name  
        The foil of _get_conc  
        params:  
            str chem_name: the chemical name to strip a reagent name from  
        returns:  
            str: the reagent name parsed from the chem_name  
        '''
        
        return chem_name[:re.search('C\d*\.\d*$', chem_name).start()]

    #a dictionary to assign priorities to different labwares. Right now used only to prioritize
    #platereader when no other labware has been specified
    _exec_init_containers.priority = defaultdict(lambda: 100)
    _exec_init_containers.priority['platereader4'] = 1
    _exec_init_containers.priority['platereader7'] = 2

    @error_exit
    def execute(self, command_type, cid, arguments):
        if command_type == 'close':
            self._exec_close(cid)
            return 0
        else:
            assert (command_type in self.exec_funcs), "Unidentified command '{}'".format(command_type)
            if arguments:
                return self.exec_funcs[command_type](self, *arguments, cid=cid)
            else:
                return self.exec_funcs[command_type](self, cid=cid)
    
    @exec_func('home', 1, True, exec_funcs)
    def _exec_home(self,*args):
        '''
        homes the robot. Takes args for compatibility only  
        '''
        self.protocol.home()

    @exec_func('mix', 1, True, exec_funcs)
    def _exec_mix(self, mix_list):
        '''
        executes a mix command.  
        params:  
            list<tuple<str, int>> mix_list: list of chem_names to be mixed with a code for the 
              type of mix to be performed.  
        Postconditions:  
            every well in the mix_list has been mixed.  
            pipette tips were replaced if they were dirty with something else before  
        '''
        for chem_name, mix_code in mix_list:
            self._mix(chem_name, mix_code)

    def _mix(self, chem_name, mix_code):
        '''
        mix a well mix_code relates to how thorough  
        params:  
            str chem_name: the name of the chemical to mix  
            int mix_code: 1 is normal 2 is 'for real'  
        Postconditions:  
            Well has been mixed.  
            pipette tips were replaced if they were dirty with something else before  
        '''
        for arm in self.pipettes.keys():
            if self.pipettes[arm]['last_used'] not in ['WaterC1.0', 'clean', chem_name]:
                self._get_clean_tips()
                break; #cause now they're clean
        for arm_to_check in self.pipettes.keys():
            #this is really easy to fix, but it should not be fixed here, it should be fixed in a
            #higher level function call. This is minimal step for maximum speed.
            assert (self.pipettes[arm_to_check]['last_used'] in ['clean', 'WaterC1.0', chem_name]), "trying to transfer {}->{}, with {} arm, but {} arm was dirty with {}".format(chem_name, dst, arm, arm_to_check, self.pipettes[arm_to_check]['last_used'])
        self.protocol._commands.append('HEAD: {} : mixing {} '.format(datetime.now(pytz.timezone('US/Pacific')).strftime('%d-%b-%Y %H:%M:%S:%f'), chem_name))
        arm = self._get_preffered_pipette(300) #gets the larger pipette
        pipette = self.pipettes[arm]['pipette']
        self.pipettes[arm]['last_used'] = chem_name #gotta update the last used
        cont = self.containers[chem_name]
        #perform the mix
        cont.mix(pipette, self.pipettes[arm]['size'], mix_code)
        
        #pull a little out of that well and shake off the drops
        pipette.well_bottom_clearance.dispense = cont.disp_height
        #blowout
        for i in range(4):
            pipette.blow_out()
        #wiggle - touch tip (spin fast inside well)
        pipette.touch_tip(radius=0.3,speed=40)

    def _get_necessary_vol(self, mass, molar_mass, conc):
        '''
        helper func for _exec_make to get the necessary volume of water to turn this into
        a reagent  
        params:  
            float mass: the mass of the powder  
            float molar_mass: the molar mass of reagent  
            float conc: the desired concentration  
        returns:  
            float: the volume of water needed to create reagent
        '''
        milimols = 1000 * mass/molar_mass
        vol = milimols/conc * 1e6 #microliter conversion
        return vol

    @exec_func('make', 1, True, exec_funcs)
    def _exec_make(self, name, conc):
        '''
        creates a new reagent with chem name and conc  
        params:  
            str name: the name of the chemical without C<conc>  
            float conc: the concentration of the chemical  
        Postconditions:  
            a container has been popped from dry_containers and the container for this chem name
              has been replaced by the dry_container.  
            Water has been transfered into the dry_container.  
            The concentration of the dry_container has been updated.  
            Name for dry_container has been updated to chem_name.  
        '''
        chem_name = "{}C{}".format(name, conc)
        #find a replacement that has enough volume to be diluted
        replacement = None #container to fill to replace old solution
        vol = 0
        i=0
        while not replacement:
            try:
                dry_cont, mass, molar_mass = self.dry_containers[name][i]
            except IndexError:
                raise Exception("Ran out of dry ingredients to restock {}, or can't dilute \
                        enough to restock".format(chem_name))
            vol = self._get_necessary_vol(mass, molar_mass, conc)
            if vol < dry_cont.MAX_VOL and vol > dry_cont.DEAD_VOL:
                replacement = self.dry_containers[name].pop(i)[0]
            i+= 1
        #overwrite the container with the replacement
        self.containers[chem_name] = replacement
        #update some things you didn't know when you initialized
        self.containers[chem_name].conc = conc
        self.containers[chem_name].name = chem_name
        #figure out what your water source should be
        is_cold = self.containers[chem_name].labware.name == 'temp_mod_24_tube'
        water_src = 'ColdWaterC1.0' if is_cold else 'WaterC1.0'
        #dilute the thing
        self._exec_transfer(water_src,[(chem_name,vol)])
        #rewrite history (since first entry is water instead of what we want)
        self.containers[chem_name].rewrite_history_first()
        #mix
        self._mix(chem_name, 2)

    @exec_func('loc_req', 1, False, exec_funcs)
    def _exec_loc_req(self, wellnames):
        '''
        processes a request for locations of wellnames and sends a response with their locations  
        params:  
            list<str>|str wellnames: requested wells or the string 'all' as specified 
              in armchair documentation  
        returns:  
            list<tuple<str,str,int>: chem_name, well_loc, deck_pos. see armchair specs  
        '''
        response = []
        #permits the str all of wellnames
        wellnames = self.containers.keys() if wellnames == 'all' else wellnames
        for name in wellnames:
            cont = self.containers[name]
            response.append((name,
                    cont.loc,
                    cont.deck_pos,
                    cont.vol,
                    cont.aspiratible_vol))
        self.portal.send_pack('loc_resp', response)

    @exec_func('pause', 1, True, exec_funcs)
    def _exec_pause(self, pause_time):
        '''
        executes a pause command by waiting for 'time' seconds  
        params:  
            float pause_time: time to wait in seconds  
        '''
        #no need to pause for a simulation
        if not self.simulate:
            time.sleep(pause_time)

    @exec_func('transfer', 1, True, exec_funcs)
    def _exec_transfer(self, src, transfer_steps):
        '''
        this command executes a transfer. 
        params:  
            str src: the chem_name of the source well  
            list<tuple<str,float>> transfer_steps: each element is a dst, vol pair  
        '''
        #check to make sure that both tips are not dirty with a chemical other than the one you will pipette
        for arm in self.pipettes.keys():
            if self.pipettes[arm]['last_used'] not in ['WaterC1.0', 'clean', src]:
                self._get_clean_tips()
                break; #cause now they're clean
        for dst, vol in transfer_steps:
            self._transfer_step(src,dst,vol)
            new_tip=False #don't want to use a new tip_next_time

    @exec_func('stop', 1, True, exec_funcs)
    def _exec_stop(self):
        '''
        executes a stop command by creating a TCP connection, telling the controller to get
        user input, and then waiting for controller response
        '''
        self.protocol.home()
        self.portal.send_pack('stopped')
        pack_type, _, _ = self.portal.recv_pack()
        assert (pack_type == 'continue'), "Was stopped waiting for continue, but recieved, {}".format(pack_type)

    def _transfer_step(self, src, dst, vol):
        '''
        used to execute a single tranfer from src to dst. Handles things like selecting
        appropriately sized pipettes. If you need
        more than 1 step, will facilitate that  
        params:  
            str src: the chemical name to pipette from  
            str dst: thec chemical name to pipette into  
            float vol: the volume to pipette  
        '''
        #choose your pipette
        arm = self._get_preffered_pipette(vol)
        #the fudge factor makes sure that if exactly 300 300//300 + 1 = 1 not 2
        n_substeps = int((vol-1e-9) // self.pipettes[arm]['size']) + 1
        substep_vol = vol / n_substeps
        
        #transfer the liquid in as many steps are necessary
        for i in range(n_substeps):
            self._liquid_transfer(src, dst, substep_vol, arm)
        self.dump_well_histories()
        return

    def _get_clean_tips(self):
        '''
        checks if the both tips to see if they're dirty. Drops anything that's dirty, then picks
        up clean tips  
        params:  
            str ok_chems: if you're ok reusing the same tip for this chemical, no need to replace  
        '''
        drop_list = [] #holds the pipettes that were dirty
        #drop first so no sprinkles get on rack while picking up
        ok_list = ['clean','WaterC1.0']
        for arm in self.pipettes.keys():
            print(self.pipettes[arm]['last_used'])
            if self.pipettes[arm]['last_used'] not in ok_list:
                self.pipettes[arm]['pipette'].drop_tip()
                drop_list.append(arm)
        #now that you're clean, you can pick up new tips
        for arm in drop_list:
            print(self.pipettes[arm])
            print(self.pipettes[arm]['pipette'])
            print(self.pipettes[arm]['pipette'].tip_racks)
            self.pipettes[arm]['pipette'].pick_up_tip()
            self.pipettes[arm]['last_used'] = 'clean'
        
   

    def _get_preffered_pipette(self, vol):
        '''
        returns the pipette with size, or one smaller  
        params:  
            float vol: the volume to be transfered in uL  
        returns:  
            str: in ['right', 'left'] the pipette arm you're to use  
        '''
        preffered_size = 0
        if vol < 40.0:
            preffered_size = 20.0
        elif vol < 1000:
            preffered_size = 300.0
        else:
            preffered_size = 1000.0
        
        #which pipette arm has a larger pipette?
        larger_pipette=None
        if self.pipettes['right']['size'] < self.pipettes['left']['size']:
            larger_pipette = 'left'
            smaller_pipette = 'right'
        else:
            larger_pipette = 'right'
            smaller_pipette = 'left'

        FUDGE_FACTOR = 0.0001
        if self.pipettes[larger_pipette]['size'] <= preffered_size + FUDGE_FACTOR:
            #if the larger one is small enough return it
            return larger_pipette
        else:
            #if the larger one is too large return the smaller
            return smaller_pipette

    def _liquid_transfer(self, src, dst, vol, arm):
        '''
        the lowest of the low. Transfer liquid from one container to another. And mark the tip
        as dirty with src, and update the volumes of the containers it uses  
        params:  
            str src: the chemical name of the source container  
            str dst: the chemical name of the destination container  
            float vol: the volume of liquid to be transfered  
            str arm: the robot arm to use for this transfer  
        Postconditions:
            vol uL of src has been transfered to dst  
            pipette has been adjusted to be dirty with src  
            volumes of src and dst have been updated  
        Preconditions:
            Both pipettes are clean or of same type  
            src has enough volume to transfer
        '''
        for arm_to_check in self.pipettes.keys():
            #this is really easy to fix, but it should not be fixed here, it should be fixed in a
            #higher level function call. This is minimal step for maximum speed.
            assert (self.pipettes[arm_to_check]['last_used'] in ['clean', 'WaterC1.0', src]), "trying to transfer {}->{}, with {} arm, but {} arm was dirty with {}".format(src, dst, arm, arm_to_check, self.pipettes[arm_to_check]['last_used'])
        self.protocol._commands.append('HEAD: {} : transfering {} to {}'.format(datetime.now(pytz.timezone('US/Pacific')).strftime('%d-%b-%Y %H:%M:%S:%f'), src, dst))
        pipette = self.pipettes[arm]['pipette']
        src_cont = self.containers[src] #the src container
        dst_cont = self.containers[dst] #the dst container

        sufficient_vol = False
        #attempt to aspirate and make if you can't
        while not sufficient_vol:
            try:
                src_cont.aspirate(vol, pipette, self.lab_deck)
                #pipette is now dirty
                self.pipettes[arm]['last_used'] = src
                sufficient_vol=True
            except EmptyReagent as e:
                src_raw_name = self._get_reagent(e.chem_name)
                src_conc = self._get_conc(e.chem_name)
                try:
                    print('<<eve>> ran out of {}. Attempting to make more'.format(src))
                    self._exec_make(src_raw_name, src_conc)
                except:
                    raise e
        #update the pipette to be dirty
        self.pipettes[arm]['last_used'] = src
        #dispense into destination container
        dst_cont.dispense(vol, pipette, self.lab_deck, src)

    def dump_well_map(self):
        '''
        dumps the well_map to a file
        '''
        path=os.path.join(self.logs_p,'wellmap.tsv')
        names = self.containers.keys()
        locs = []
        deck_poses = []
        vols = []
        chem_names = []
        container_types = []
        for name in names:
            cont = self.containers[name]
            if isinstance(cont, MultiContainer):
                #this is one of the few instances where the loc, deck_pos, and vol
                #you want is not the attribute of the current cont for this multicontainer
                #instead, you want a list of all of the raw containers.
                for subcont in cont.cont_list:
                    locs.append(subcont.loc)
                    deck_poses.append(subcont.deck_pos)
                    vols.append(subcont.vol)
                    chem_names.append(name)
                    container_types.append(
                            self.lab_deck[cont.deck_pos].get_container_type(cont.loc)
                            )
            else:
                #is just a regular container
                locs.append(cont.loc)
                deck_poses.append(cont.deck_pos)
                vols.append(cont.vol)
                chem_names.append(name)
                container_types.append(
                        self.lab_deck[cont.deck_pos].get_container_type(cont.loc)
                        )
        well_map = pd.DataFrame({'chem_name':list(chem_names), 'loc':locs, 'deck_pos':deck_poses, 
                'vol':vols,'container':container_types})
        well_map.sort_values(by=['deck_pos', 'loc'], inplace=True)
        well_map.to_csv(path, index=False, sep='\t')

    def dump_protocol_record(self):
        '''
        dumps the protocol record to tsv
        '''
        path=os.path.join(self.logs_p, 'protocol_record.txt')
        command_str = ''.join(x+'\n' for x in self.protocol.commands())[:-1]
        with open(path, 'w') as command_dump:
            command_dump.write(command_str)

    def dump_well_histories(self):
        '''
        gathers the history of every reaction and puts it in a single df. Writes that df to file
        '''
        path=os.path.join(self.logs_p, 'well_history.tsv')
        histories=[]
        for name, container in self.containers.items():
            df = pd.DataFrame(container.history, columns=['timestamp', 'chemical', 'vol'])
            df['container'] = name
            histories.append(df)
        all_history = pd.concat(histories, ignore_index=True)
        all_history['timestamp'] = pd.to_datetime(all_history['timestamp'], format='%d-%b-%Y %H:%M:%S:%f')
        all_history.sort_values(by=['timestamp'], inplace=True)
        all_history.reset_index(inplace=True, drop=True)
        all_history.to_csv(path, index=False, sep='\t')

    def exception_handler(self, e):
        '''
        code to handle all exceptions.  
        Procedure:
            Dump a locations of all of the chemicals  
        '''
        pass

    @exec_func('close', 0, False, exec_funcs)
    def _exec_close(self, cid):
        '''
        close the connection in a nice way
        Postconditions:  
          tips have been dropped, temp module is off, socket is closed  
        '''
        print('<<eve>> initializing breakdown')
        #shutdown temperature controller
        if self.temp_module:
            self.temp_module.deactivate()
        #drop pipettes
        for arm_dict in self.pipettes.values():
            pipette = arm_dict['pipette']
            pipette.drop_tip()
        self.protocol.home()
        self.portal.send_pack('ready', cid)
        #kill link
        print('<<eve>> shutting down')
        self.portal.close()

    @exec_func('save', 1, False, exec_funcs)
    def _exec_save(self):
        '''
        saves state, and then ships files back to controller over FTP  
        '''
        #write logs
        self.dump_protocol_record()
        self.dump_well_histories()
        self.dump_well_map()
        #ship logs
        filenames = list(os.listdir(self.logs_p))
        filepaths = [os.path.join(self.logs_p, filename) for filename in filenames]
        self.portal.send_ftp(filepaths)
        
    def _error_handler(self, e):
        try:
            print('''<<eve>> ----------------Eve Errror--------------
            Sending Error packet''')
            self.portal.send_pack('error', e)
            print('<<eve>> Waiting on close')
            self.portal.recv_first('save')
            self._exec_save()
            pack_type, cid, payload = self.portal.recv_first('close')
            self._exec_close(cid)
        finally:
            time.sleep(2) #this is just for printing format. Not critical
            raise e

def launch_eve_server(**kwargs):
    '''
    launches an eve server to create robot, connect to controller etc  
    **kwargs:  
        + str my_ip: the ip address to launch the server on. required arg  
        + threading.Barrier barrier: if specified, will launch as a thread instead of a main  
    '''
    my_ip = kwargs['my_ip']
    PORT_NUM = 50000
    #construct a socket
    sock = socket.socket(socket.AF_INET)
    sock.setsockopt(socket.SOL_SOCKET,socket.SO_REUSEADDR,1)
    sock.bind((my_ip,PORT_NUM))
    print('<<eve>> listening on port {}'.format(PORT_NUM))
    sock.listen(5)
    if kwargs['barrier']:
        #running in thread mode with barrier. Barrier waits for both threads
        kwargs['barrier'].wait()
    client_sock, client_addr = sock.accept()
    print('<<eve>> connected')
    buffered_sock = BufferedSocket(client_sock, timeout=None)
    portal = Armchair(buffered_sock,'eve','Armchair_Logs')
    eve = None
    pack_type, cid, args = portal.recv_pack()
    if pack_type == 'init':
        simulate, using_temp_ctrl, temp, labware_df, instruments, reagents_df, controller_ip, dry_containers_df = args
        #I don't know why this line is needed, but without it, Opentrons crashes because it doesn't
        #like to be run from a thread
        asyncio.set_event_loop(asyncio.new_event_loop())
        eve = OT2Robot(simulate, using_temp_ctrl, temp, labware_df, instruments, reagents_df,my_ip, controller_ip, portal, dry_containers_df)
        portal.send_pack('ready', cid)
    connection_open=True
    while connection_open:
        pack_type, cid, payload = portal.recv_pack()
        connection_open = eve.execute(pack_type, cid, payload)
    sock.close()
    return



def hack_to_get_ip():
    '''
    author @zags from stack overflow
    courtesy of stack overflow
    '''
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.connect(("8.8.8.8", 80))
    my_ip = s.getsockname()[0]
    s.close()
    return my_ip

if __name__ == '__main__':
    #my_ip = hack_to_get_ip()
    my_ip = "169.254.44.249"
    fail_count = 0
    while True:
        try:
            launch_eve_server(my_ip=my_ip, barrier=None)
            fail_count = 0
        except Exception as e:
            fail_count+=1
            print("ot2_robot code encountered exception '{}' in ot2_robot. Traceback will be written to ot2_error_output.txt. Excepting and launching new server.".format(e))
            #credit Horacio of stack overflow
            with open('ot2_error_output.txt', 'a+') as file:
                file.write("{}\n".format(datetime.now(pytz.timezone('US/Pacific')).strftime('%d-%b-%Y %H:%M:%S:%f')))
                file.write(str(e))
                file.write(traceback.format_exc())
        finally:
            if fail_count > 3:
                raise e
