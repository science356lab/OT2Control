from abc import ABC
from abc import abstractmethod
from collections import defaultdict
from datetime import datetime
import socket
import json
import dill
import math
import os
import shutil
import webbrowser
from tempfile import NamedTemporaryFile

import gspread
from df2gspread import df2gspread as d2g
from df2gspread import gspread2df as g2d
from oauth2client.service_account import ServiceAccountCredentials
import pandas as pd
import numpy as np
import opentrons.execute
from opentrons import protocol_api, simulate, types
from boltons.socketutils import BufferedSocket

import Armchair.armchair as armchair

#For Debugging
USE_CACHE = False
#USE_CACHE = True
CACHE_PATH = 'Cache'

#this has two keys, 'deck_pos' and 'loc'. They map to the plate reader and the loc on that plate
#reader given a regular loc for a 96well plate.
#Please do not read this. paste it into a nice json viewer.
PLATEREADER_INDEX_TRANSLATOR = { "deck_pos":{ "A1":"platreader4", "A2":"p4", "A3":"p4", "A4":"p4", "A5":"p4", "A13":"platereader7", "A11":"p7", "A10":"p7", "A9":"p7", "A8":"p7", "A7":"p7", "A6":"p7", "B1":"p4", "B2":"p4", "B3":"p4", "B4":"p4", "B5":"p4", "B6":"p7", "B7":"p7", "B8":"p7", "B9":"p7", "B10":"p7", "B11":"p7", "B12":"p7", "C1":"p4", "C2":"p4", "C3":"p4", "C4":"p4", "C5":"p4", "C6":"p7", "C7":"p7", "C8":"p7", "C9":"p7", "C10":"p7", "C11":"p7", "C12":"p7", "D1":"p4", "D2":"p4", "D3":"p4", "D4":"p4", "D5":"p4", "D6":"p7", "D7":"p7", "D8":"p7", "D9":"p7", "D10":"p7", "D11":"p7", "D12":"p7", "E1":"p4", "E2":"p4", "E3":"p4", "E4":"p4", "E5":"p4", "E6":"p7", "E7":"p7", "E8":"p7", "E9":"p7", "E10":"p7", "E11":"p7", "E12":"p7", "F1":"p4", "F2":"p4", "F3":"p4", "F4":"p4", "F5":"p4", "F6":"p7", "F7":"p7", "F8":"p7", "F9":"p7", "F10":"p7", "F11":"p7", "F12":"p7", "G1":"p4", "G2":"p4", "G3":"p4", "G4":"p4", "G5":"p4", "G6":"p7", "G7":"p7", "G8":"p7", "G9":"p7", "G10":"p7", "G11":"p7", "G12":"p7", "H1":"p4", "H2":"p4", "H3":"p4", "H4":"p4", "H5":"p4", "H6":"p7", "H7":"p7", "H8":"p7", "H9":"p7", "H10":"p7", "H11":"p7", "H12":"p7" }, "loc":{ "A1":"E1", "A2":"D1", "A3":"C1", "A4":"B1", "A5":"A1", "A13":"A1", "A11":"B1", "A10":"C1", "A9":"D1", "A8":"E1", "A7":"F1", "A6":"G1", "B1":"E2", "B2":"D2", "B3":"C2", "B4":"B2", "B5":"A2", "B6":"G2", "B7":"F2", "B8":"E2", "B9":"D2", "B10":"C2", "B11":"B2", "B12":"A2", "C1":"E3", "C2":"D3", "C3":"C3", "C4":"B3", "C5":"A3", "C6":"G3", "C7":"F3", "C8":"E3", "C9":"D3", "C10":"C3", "C11":"B3", "C12":"A3", "D1":"E4", "D2":"D4", "D3":"C4", "D4":"B4", "D5":"A4", "D6":"G4", "D7":"F4", "D8":"E4", "D9":"D4", "D10":"C4", "D11":"B4", "D12":"A4", "E1":"E5", "E2":"D5", "E3":"C5", "E4":"B5", "E5":"A5", "E6":"G5", "E7":"F5", "E8":"E5", "E9":"D5", "E10":"C5", "E11":"B5", "E12":"A5", "F1":"E6", "F2":"D6", "F3":"C6", "F4":"B6", "F5":"A6", "F6":"G6", "F7":"F6", "F8":"E6", "F9":"D6", "F10":"C6", "F11":"B6", "F12":"A6", "G1":"E7", "G2":"D7", "G3":"C7", "G4":"B7", "G5":"A7", "G6":"G7", "G7":"F7", "G8":"E7", "G9":"D7", "G10":"C7", "G11":"B7", "G12":"A7", "H1":"E8", "H2":"D8", "H3":"C8", "H4":"B8", "H5":"A8", "H6":"G8", "H7":"F8", "H8":"E8", "H9":"D8", "H10":"C8", "H11":"B8", "H12":"A8" }}

#VISUALIZATION
def df_popout(df):
    '''
    Neat trick for viewing df as html in browser
    With some minor tweaks
    Credit to Stack Overflow
    @author Shovalt
    '''
    with NamedTemporaryFile(delete=False, suffix='.html') as f:
        html_str = df.to_html()
        f.write(str.encode(html_str,'ascii'))
    webbrowser.open(f.name)

#CLIENT
def pre_rxn_questions():
    '''
    asks user for control params
    returns:
        bool simulate: true if behaviour is to be simulated instead of executed
        str rxn_sheet_name: the title of the google sheet
        bool using_temp_ctrl: true if planning to use temperature ctrl module
        float temp: the temperature you want to keep the module at
    '''
    simulate = (input('<<controller>> Simulate or Execute: ').lower() == 'simulate')
    rxn_sheet_name = input('<<controller>> Enter Sheet Name as it Appears on the Spreadsheets Title: ')
    temp_ctrl_response = input('<<controller>> Are you using the temperature control module, yes or no?\
    (if yes, turn it on before responding): ').lower()
    using_temp_ctrl = ('y' == temp_ctrl_response or 'yes' == temp_ctrl_response)
    temp = None
    if using_temp_ctrl:
        temp = input('<<controller>> What temperature in Celcius do you want the module \
        set to? \n (the protocol will not proceed until the set point is reached) \n')
    return simulate, rxn_sheet_name, using_temp_ctrl, temp

def open_sheet(rxn_sheet_name, credentials):
    '''
    open the google sheet
    params:
        str rxn_sheet_name: the title of the sheet to be opened
        oauth2client.ServiceAccountCredentials credentials: credentials read from a local json
    returns:
        gspread.Spreadsheet the spreadsheet (probably of all the reactions)

    '''
    gc = gspread.authorize(credentials)
    try:
        wks = gc.open(rxn_sheet_name)
    except: 
        raise Exception('Spreadsheet Not Found: Make sure the spreadsheet name is spelled correctly and that it is shared with the robot ')
    return wks

def init_credentials(rxn_sheet_name):
    '''
    this function reads a local json file to get the credentials needed to access other funcs
    params:
        str rxn_sheet_name: the name of the reaction sheet to run
    returns:
        ServiceAccountCredentials: the credentials to access that sheet
    '''
    scope = ['https://spreadsheets.google.com/feeds',
             'https://www.googleapis.com/auth/drive']
    #get login credentials from local file. Your json file here
    path = 'Credentials/hendricks-lab-jupyter-sheets-5363dda1a7e0.json'
    credentials = ServiceAccountCredentials.from_json_keyfile_name(path, scope) 
    return credentials

def get_wks_key(credentials, rxn_sheet_name):
    '''
    open and search a sheet that tells you which sheet is associated with the reaction
    params:
        ServiceAccountCredentials credentials: to access the sheets
        str rxn_sheet_name: the name of sheet
    returns:
        str wks_key: the key associated with the sheet. It functions similar to a url
    '''
    #DEBUG
    if USE_CACHE:
        #load cache
        with open(os.path.join(CACHE_PATH, 'name_key_pairs.pkl'), 'rb') as name_key_pairs_cache:
            name_key_pairs = dill.load(name_key_pairs_cache)
    else:
        #pull down data
        gc = gspread.authorize(credentials)
        name_key_wks = gc.open_by_url('https://docs.google.com/spreadsheets/d/1m2Uzk8z-qn2jJ2U1NHkeN7CJ8TQpK3R0Ai19zlAB1Ew/edit#gid=0').get_worksheet(0)
        name_key_pairs = name_key_wks.get_all_values() #list<list<str name, str key>>
        #Note the key is a unique identifier that can be used to access the sheet
        #d2g uses it to access the worksheet
        
        #DEBUG
        #dump to cache
        with open(os.path.join(CACHE_PATH, 'name_key_pairs.pkl'), 'wb') as name_key_pairs_cache:
            dill.dump(name_key_pairs, name_key_pairs_cache)
    try:
        i=0
        wks_key = None
        while not wks_key and i < len(name_key_pairs):
            row = name_key_pairs[i]
            if row[0] == rxn_sheet_name:
                wks_key = row[1]
            i+=1
    except IndexError:
        raise Exception('Spreadsheet Name/Key pair was not found. Check the dict spreadsheet \
        and make sure the spreadsheet name is spelled exactly the same as the reaction \
        spreadsheet.')
    return wks_key

def load_rxn_table(rxn_spreadsheet, rxn_sheet_name):
    '''
    reaches out to google sheets and loads the reaction protocol into a df and formats the df
    adds a chemical name (primary key for lots of things. e.g. robot dictionaries)
    renames some columns to code friendly as opposed to human friendly names
    params:
        gspread.Spreadsheet rxn_spreadsheet: the sheet with all the reactions
        str rxn_sheet_name: the name of the spreadsheet
    returns:
        pd.DataFrame: the information in the rxn_spreadsheet w range index. spreadsheet cols
        Dict<str,list<str,str>>: effectively the 2nd and 3rd rows in excel. Gives 
                labware and container preferences for products
    '''
    if USE_CACHE:
        with open(os.path.join(CACHE_PATH,'rxn_wks_data.pkl'), 'rb') as rxn_wks_data_cache:
            data = dill.load(rxn_wks_data_cache)
    else:
        rxn_wks = rxn_spreadsheet.get_worksheet(0)
        data = rxn_wks.get_all_values()
        with open(os.path.join(CACHE_PATH,'rxn_wks_data.pkl'),'wb') as rxn_wks_data_cache:
            dill.dump(data, rxn_wks_data_cache)
    cols = make_unique(pd.Series(data[0])) 
    rxn_df = pd.DataFrame(data[3:], columns=cols)
    #rename some of the clunkier columns 
    rxn_df.rename({'operation':'op', 'dilution concentration':'dilution_conc','concentration (mM)':'conc', 'reagent (must be uniquely named)':'reagent', 'Pause before addition?':'pause', 'comments (e.g. new bottle)':'comments'}, axis=1, inplace=True)
    rxn_df.drop(columns=['comments'], inplace=True)#comments are for humans
    rxn_df.replace('', np.nan,inplace=True)
    #rename chemical names
    rxn_df['chemical_name'] = rxn_df[['conc', 'reagent']].apply(get_chemical_name,axis=1)
    rename_products(rxn_df)
    #go back for some non numeric columns
    rxn_df['callbacks'].fillna('',inplace=True)
    #create labware_dict
    cols = rxn_df.columns.to_list()
    product_start_i = cols.index('reagent')+1
    requested_labware = data[1][product_start_i+1:]#add one to account for the first col (labware).
    requested_containers = data[2][product_start_i+1:]
    #in df this is an index, so size cols is one less
    products_to_labware = {product:[labware,container] for product, labware, container in zip(cols[product_start_i:], requested_labware,requested_containers)}
    products = products_to_labware.keys()
    #make the reagent columns floats
    rxn_df.loc[:,products] =  rxn_df[products].astype(float)
    rxn_df.loc[:,products] = rxn_df[products].fillna(0)
    return rxn_df, products_to_labware

def rename_products(rxn_df):
    '''
    renames dilutions acording to the reagent that created them
    and renames rxns to have a concentration
    Preconditions:
        dilution cols are named dilution_1/2 etc
        callback is the last column in the dataframe
    params:
        df rxn_df: the dataframe with all the reactions
    Postconditions:
        the df has had it's dilution columns renamed to the chemical used to produce it + C<conc>
        rxn columns have C1 appended to them
    '''
    dilution_cols = [col for col in rxn_df.columns if 'dilution_placeholder' in col]
    #get the rxn col names
    rxn_cols = rxn_df.loc[:, 'reagent':'chemical_name'].drop(columns=['reagent','chemical_name']).columns
    rename_key = {}
    for col in rxn_cols:
        if 'dilution_placeholder' in col:
            row = rxn_df.loc[~rxn_df[col].isna()].squeeze()
            reagent_name = row['chemical_name']
            name = reagent_name[:reagent_name.rfind('C')+1]+row['dilution_conc']
            rename_key[col] = name
        else:
            rename_key[col] = "{}C1".format(col)

    rxn_df.rename(rename_key, axis=1, inplace=True)

def get_chemical_name(row):
    '''
    create a chemical name
    from a row in a pandas df. (can be just the two columns, ['conc', 'reagent'])
    params:
        pd.Series row: a row in the rxn_df
    returns:
        chemical_name: the name for the chemical "{}C{}".format(name, conc) or name if
          has no concentration, or nan if no name
    '''
    if pd.isnull(row['reagent']):
        #this must not be a transfer. this operation has no chemical name
        return np.nan
    elif pd.isnull(row['conc']):
        #this uses a chemical, but the chemical doesn't have a concentration (probably a mix)
        return row['reagent'].replace(' ', '_')
    else:
        #this uses a chemical with a conc. Probably a stock solution
        return "{}C{}".format(row['reagent'], row['conc']).replace(' ', '_')
    return pd.Series(new_cols)


def init_robot(portal, rxn_spreadsheet, rxn_df, simulate, spreadsheet_key, credentials, using_temp_ctrl, temp, products_to_labware):
    '''
    this is basically a wrapper for get_robot_params. It calls get_robot_params and then ships
    the return values to the robot along with some other stuff you passed in.
    params:
        Armchair portal: the armchair object connected to robot
        gspread.Spreadsheet rxn_spreadsheet: a spreadsheet object with second sheet having
          deck positions
        df rxn_df: the input df read from sheets
        bool simulate: if the robot is to simulate or execute
        str spreadsheet_key: this is the a unique id for google sheet used for i/o with sheets
        ServiceAccount Credentials credentials: to access sheets
        bool using_temp_ctrl: true if temp control should be used
        float temp: the temperature to keep the module at
        Dict<str, str>: maps rxns to prefered labware
    Postconditions:
        user has been queried about reagents and response has been pulled down
    '''
    reagents, labware_df, instruments, product_df = get_robot_params(rxn_spreadsheet, rxn_df, spreadsheet_key, credentials, products_to_labware)
    #send robot data to initialize itself
    cid = portal.send_pack('init', simulate, using_temp_ctrl, temp, labware_df, instruments, reagents)
    
    inflight_packs = [cid]
    block_on_ready(inflight_packs, portal)

    #send robot data to initialize empty product containers. Because we know things like total
    #vol and desired labware, this makes sense for a planned experiment
    with open('product_df_cache.pkl', 'wb') as cache:
        dill.dump(product_df, cache)
    cid = portal.send_pack('init_containers', product_df)
    inflight_packs.append(cid)
    block_on_ready(inflight_packs,portal)
    return

def get_robot_params(rxn_spreadsheet, rxn_df, spreadsheet_key, credentials, products_to_labware):
    '''
    This function gets the unique reagents, interfaces with the docs to get details on those
      reagents, and returns that information so it can be sent to robot
    params:
        Armchair portal: the armchair object connected to robot
        gspread.Spreadsheet rxn_spreadsheet: a spreadsheet object with second sheet having
          deck positions
        df rxn_df: the input df read from sheets
        bool simulate: if the robot is to simulate or execute
        str spreadsheet_key: this is the a unique id for google sheet used for i/o with sheets
        ServiceAccount Credentials credentials: to access sheets
        bool using_temp_ctrl: true if temp control should be used
        float temp: the temperature to keep the module at
        Dict<str, str>: maps rxns to prefered labware
    returns:
        df reagents_df: info on reagents. columns from sheet. See excel specification
        df labware_df:
            str name: the common name of the labware
            str first_usable: the first tip/well to use
            int deck_pos: the position on the deck of this labware
            str empty_list: the available slots for empty tubes format 'A1,B2,...' No specific
              order
        Dict<str:str> instruments: keys are ['left', 'right'] corresponding to arm slots. vals
          are the pipette names filled in
        df product_df:
            INDEX
            the chemical names of the products
            COLS
            str labware: type of labware to use
            float max_vol: the maximum volume that will be in this container at any time
    '''
    #query the docs for more info on reagents
    construct_reagent_sheet(rxn_df, spreadsheet_key, credentials)

    #pull the info into a df
    #DEBUG
    if USE_CACHE:
        #if you've already seen this don't pull it
        with open(os.path.join(CACHE_PATH, 'reagent_info_sheet.pkl'), 'rb') as reagent_info_cache:
            reagent_info = dill.load(reagent_info_cache)
    else:
        input("<<controller>> please press enter when you've completed the reagent sheet")
        #pull down from the cloud
        reagent_info = g2d.download(spreadsheet_key, 'reagent_info', col_names = True, 
            row_names = True, credentials=credentials).drop(columns=['comments'])
        #cache the data
        #DEBUG
        with open(os.path.join(CACHE_PATH, 'reagent_info_sheet.pkl'), 'wb') as reagent_info_cache:
            dill.dump(reagent_info, reagent_info_cache)
    #if there are empty tubes make a dataframe full of them
    empty_containers = reagent_info.loc['empty' == reagent_info.index].set_index('deck_pos').drop(columns=['conc', 'mass'])
    reagents = reagent_info.drop(['empty'], errors='ignore') # incase not on axis
    reagents = reagents.astype({'conc':float,'deck_pos':int,'mass':float})

    #pull labware etc from the sheets
    labware_df, instruments = get_labware_info(rxn_spreadsheet, empty_containers)

    #build_product_df with info on where to build products
    product_df = construct_product_df(rxn_df, products_to_labware)
    return reagents, labware_df, instruments, product_df

def construct_product_df(rxn_df, products_to_labware):
    '''
    Creates a df to be used by robot to initialize containers for the products it will make
    params:
        df rxn_df: as passed to init_robot
        df products_to_labware: as passed to init_robot
    returns:
        df products:
            INDEX:
            str chemical_name: the name of this rxn
            COLS:
            str labware: the labware to put this rxn in or None if no preference
            float max_vol: the maximum volume that will ever ocupy this container
    TODO great place to catch not enough liquid errors
    '''
    products = products_to_labware.keys()
    max_vols = [get_rxn_max_vol(rxn_df, product, products) for product in products]
    product_df = pd.DataFrame(products_to_labware, index=['labware','container']).T
    product_df['max_vol'] = max_vols
    return product_df

def get_rxn_max_vol(rxn_df, name, products):
    '''
    Preconditions:
        volume in a container can change only during a 'transfer' or 'dilution'. Easy to add more
        by changing the vol_change_rows
    params:
        df rxn_df: as returned by load_table. Should have all NaN removed from products
        str name: the column name to be searched
        list<str> products: the column names of all reagents (we could look this up in rxn_df, but
          convenient to pass it in)
    returns:
        float: the maximum volume that this container will ever hold at one time, not taking into 
          account aspirations for dilutions
    '''
    #TODO handle dilutions into
    #current solution is to assume a solution is never aspirated during a dilution which
    #will assume larger than necessary volumes
    vol_change_rows = rxn_df.loc[rxn_df['op'].apply(lambda x: x in ['transfer','dilution'])]
    aspirations = vol_change_rows['chemical_name'] == name
    max_vol = 0
    current_vol = 0
    for i, is_aspiration in aspirations.iteritems():
        if is_aspiration and rxn_df.loc[i,'op'] == 'transfer':
            #This is a row where we're transfering from this well
            current_vol -= rxn_df.loc[i, products].sum()
        else:
            current_vol += rxn_df.loc[i,name]
            max_vol = max(max_vol, current_vol)
    return max_vol

def construct_reagent_sheet(rxn_df, spreadsheet_key, credentials):
    '''
    query the user with a reagent sheet asking for more details on locations of reagents, mass
    etc
    Preconditions:
        see excel_spreadsheet_preconditions.txt
    PostConditions:
        reagent_sheet has been constructed
    '''
    rxn_names = rxn_df.loc[:, 'reagent':'chemical_name'].drop(columns=['reagent','chemical_name']).columns
    reagent_df = rxn_df[['chemical_name', 'conc']].groupby('chemical_name').first()
    reagent_df.drop(rxn_names, errors='ignore', inplace=True) #not all rxns are reagents
    reagent_df[['loc', 'deck_pos', 'mass', 'comments']] = ''
    #DEBUG
    if not USE_CACHE:
        d2g.upload(reagent_df.reset_index(),spreadsheet_key,wks_name = 'reagent_info', row_names=False , credentials = credentials)


def get_reagent_attrs(row):
    '''
    proccess the df into an index of unique col names corresponding to volumes
    from a row in a pandas df. (can be just the two columns, ['conc', 'reagent'])
    params:
        pd.Series row: a row in the rxn_df
    returns:
        pd.series:
            Elements
            chemical_name: the name for the chemical "{}C{}".format(name, conc) or name if
              has no concentration, or nan if no name
            conc: the concentration of the chemical (only applicable to solutions)
            type: the type of substance this is (a classname in ot2_server_lib.py
    '''
    new_cols = {}
    if pd.isnull(row['reagent']):
        #this must not be a transfer. this operation has no chemical name
        new_cols['chemical_name'] = np.nan
        new_cols['conc'] = np.nan
        new_cols['content_type'] = np.nan
    elif pd.isnull(row['conc']):
        #this uses a chemical, but the chemical doesn't have a concentration (probably a mix)
        new_cols['chemical_name'] = row['conc'].replace(' ', '_')
        new_cols['conc'] = np.nan
        new_cols['content_type'] = 'mix'
    else:
        #this uses a chemical with a conc. Probably a stock solution
        new_cols['chemical_name'] = "{}C{}".format(row['reagent'], row['conc']).replace(' ', '_')
        new_cols['conc'] = row['conc']
        new_cols['content_type'] = 'dilution'
    return pd.Series(new_cols)

def get_labware_info(rxn_spreadsheet, empty_containers):
    '''
    Interface with sheets to get information about labware locations, first tip, etc.
    Preconditions:
        The second sheet in the worksheet must be initialized with where you've placed reagents 
        and the first thing not being used
    params:
        gspread.Spreadsheet rxn_spreadsheet: a spreadsheet object with second sheet having
          deck positions
        df empty_containers: this is used for tubes. it holds the containers that can be used
            int index: deck_pos
            str position: the position of the empty container on the labware
    returns:
        df:
          str name: the common name of the labware (made unique 
        Dict<str:str>: key is 'left' or 'right' for the slots. val is the name of instrument
    '''
    raw_labware_data = rxn_spreadsheet.get_worksheet(1).get_all_values()
    #the format google fetches this in is funky, so we convert it into a nice df
    labware_dict = {'name':[], 'first_usable':[],'deck_pos':[]}
    for row_i in range(0,10,3):
        for col_i in range(3):
            labware_dict['name'].append(raw_labware_data[row_i+1][col_i])
            labware_dict['first_usable'].append(raw_labware_data[row_i+2][col_i])
            labware_dict['deck_pos'].append(raw_labware_data[row_i][col_i])
    labware_df = pd.DataFrame(labware_dict)
    #platereader positions need to be translated, and they shouldn't be put in both
    #slots
    platereader_rows = labware_df.loc[(labware_df['name'] == 'platereader7') | \
            (labware_df['name'] == 'platereader4')]
    platereader_input_first_usable = platereader_rows.loc[\
            platereader_rows['first_usable'].astype(bool), 'first_usable'].iloc[0]
    platereader_name = PLATEREADER_INDEX_TRANSLATOR['deck_pos'][platereader_input_first_usable]
    platereader_first_usable = PLATEREADER_INDEX_TRANSLATOR['loc'][platereader_input_first_usable]
    if platereader_name == 'platereader7':
        platereader4_first_usable = 'F8'
        platereader7_firstusable = platereader_first_usable
    else:
        platereader4_first_usable = platereader_first_usable
        platereader7_first_usable = 'A1'
    labware_df.loc[labware_df['name']=='platereader4','first_usable'] = platereader4_first_usable
    labware_df.loc[labware_df['name']=='platereader7','first_usable'] = platereader7_first_usable
    labware_df = labware_df.loc[labware_df['name'] != ''] #remove empty slots
    labware_df.set_index('deck_pos', inplace=True)
    #add empty containers in list form
    #there's some fancy formating here that gets you a series with deck as the index and
    #comma seperated loc strings eg 'A1,A3,B2' as values
    grouped = empty_containers['loc'].apply(lambda pos: pos+',').groupby('deck_pos')
    labware_locs = grouped.sum().apply(lambda pos: pos[:len(pos)-1])
    labware_df = labware_df.join(labware_locs, how='left')
    labware_df['loc'] = labware_df['loc'].fillna('')
    labware_df.rename(columns={'loc':'empty_list'},inplace=True)
    labware_df.reset_index(inplace=True)
    labware_df['deck_pos'] = pd.to_numeric(labware_df['deck_pos'])
    #make instruments
    instruments = {}
    instruments['left'] = raw_labware_data[13][0]
    instruments['right'] = raw_labware_data[13][1]
    return labware_df, instruments

def run_protocol(rxn_df, portal, buff_size=4):
    '''
    takes a protocol df and sends every step to robot to execute
    params:
        df rxn_df: see excel specs
        Armchair portal: the Armchair object to communicate with the robot
        int buff: the number of commands allowed in flight at a time
    Postconditions:
        every step in the protocol has been sent to the robot
    '''
    inflight_packs = []
    product_cols = rxn_df.loc[:,'reagent':'chemical_name'].drop(
            columns=['reagent','chemical_name']).columns
    for _, row in rxn_df.iterrows():
        if row['op'] == 'transfer':
            cid = send_transfer_command(row, product_cols, portal)
            inflight_packs.append(cid)
        elif row['op'] == 'pause':
            #read through the inflight packets
            while inflight_packs:
                block_on_ready(inflight_packs, portal)
            input('<<controller>> paused. Please press enter when you\'re ready to continue')
        elif row['op'] == 'scan':
            #TODO implement scans
            pass
        elif row['op'] == 'dilution':
            #TODO implement dilutions
            pass
        else:
            raise Exception('invalid operation {}'.format(row['op']))
        #check buffer
        if len(inflight_packs) >= buff_size:
            block_on_ready(inflight_packs,portal)

def send_transfer_command(row, product_cols, portal):
    '''
    params:
        pd.Series row: a row of rxn_df
    returns:
        int: the cid of this command
    Postconditions:
        a transfer command has been sent to the robot
    '''
    src = row['chemical_name']
    containers = row[product_cols].loc[row[product_cols] != 0]
    transfer_steps = [name_vol_pair for name_vol_pair in containers.iteritems()]
    callbacks = row['callbacks'].split(',')
    cid = portal.send_pack('transfer', src, transfer_steps, callbacks)
    return cid


def block_on_ready(inflight_packs,portal):
    '''
    used to block until the server responds with a 'ready' packet
    Preconditions: inflight_packs contains cids of packets that have been sent to server, but
    not yet acknowledged
    params:
        list<int> inflight_packs: list of cids of send packets that have not been acked yet
    Postconditions:
        has stalled until a ready command was recieved.
        The cid in the ready command has been removed from inflight_packs
    '''
    pack_type, _, arguments = portal.recv_pack()
    if pack_type == 'error':
        error_handler()
    elif pack_type == 'ready':
        cid = arguments[0]
        inflight_packs.remove(cid)
    else:
        raise Exception('invalid packet type {}'.format(pack_type))
        

def close_connection(portal, ip, path='./Eve_Files'):
    '''
    runs through closing procedure with robot
    params:
        Armchair portal: the Armchair object to communicate with robot
    Postconditions:
        Log files have been written to path
        Connection has been closed
    '''
    print('<<controller>> initializing breakdown')
    if not os.path.exists(path):
        os.mkdir(path)
    portal.send_pack('close')
    #server will initiate file transfer
    pack_type, cid, arguments = portal.recv_pack()
    while pack_type == 'ready':
        #spin through all the queued ready packets
        pack_type, cid, arguments = portal.recv_pack()
    assert(pack_type == 'sending_files')
    port = arguments[0]
    filenames = arguments[1]
    sock = socket.socket(socket.AF_INET)
    sock.connect((ip, port))
    buffered_sock = BufferedSocket(sock,maxsize=4e9) #file better not be bigger than 4GB
    for filename in filenames:
        with open(os.path.join(path,filename), 'wb') as write_file:
            data = buffered_sock.recv_until(armchair.FTP_EOF)
            write_file.write(data)
    print('<<controller>> files recieved')
    sock.close()
    #server should now send a close command
    pack_type, cid, arguments = portal.recv_pack()
    assert(pack_type == 'close')
    print('<<controller>> shutting down')
    portal.close()

def error_handler():
    pass



#SERVER
#CONTAINERS
class Container(ABC):
    """
    
    Abstract container class to be overwritten for well, tube, etc.
    ABSTRACT ATTRIBUTES:
        str name: the common name we use to refer to this container
        float vol: the volume of the liquid in this container in uL
        int deck_pos: the position on the deck
        str loc: a location on the deck_pos object (e.g. 'A5')
        float conc: the concentration of the substance
        float disp_height: the height to dispense at
        float asp_height: the height to aspirate from
        list<tup<timestamp, str, float> history: the history of this container. Contents:
          timestamp timestamp: the time of the addition/removal
          str chem_name: the name of the chemical added or blank if aspiration
          float vol: the volume of chemical added/removed
    CONSTANTS:
        float DEAD_VOL: the volume at which this 
        float MIN_HEIGHT: the minimum height at which to pipette from 
    ABSTRACT METHODS:
        _update_height void: updates self.height to height at which to pipet (a bit below water line)
    IMPLEMENTED METHODS:
        update_vol(float del_vol) void: updates the volume upon an aspiration
    """

    def __init__(self, name, deck_pos, loc, vol=0,  conc=1):
        self.name = name
        self.deck_pos = deck_pos
        self.loc = loc
        self.vol = vol
        self._update_height()
        self.conc = conc
        self.history = []
        if vol:
            #create an entry with yourself as first
            self.history.append((datetime.now().strftime('%d-%b-%Y %H:%M:%S:%f'), name, vol))

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
        assert((del_vol < 0) or (name and del_vol > 0))
        self.history.append((datetime.now().strftime('%d-%b-%Y %H:%M:%S:%f'), name, del_vol))
        self.vol = self.vol + del_vol
        self._update_height()

    @property
    def disp_height(self):
        pass

    @property
    def asp_height(self):
        pass

        
class Tube20000uL(Container):
    """
    Spcific tube with measurements taken to provide implementations of abstract methods
    INHERITED ATTRIBUTES
        str name, float vol, int deck_pos, str loc, float disp_height, float asp_height
    OVERRIDDEN CONSTANTS:
        float DEAD_VOL: the volume at which this 
    INHERITED METHODS
        _update_height void, update_vol(float del_vol) void,
    """

    DEAD_VOL = 2000
    MIN_HEIGHT = 1

    def __init__(self, name, deck_pos, loc, mass=6.6699, conc=1):
        '''
        mass is defaulted to the avg_mass so that there is nothing in the container
        '''
        density_water_25C = 0.9970479 # g/mL
        avg_tube_mass15 = 6.6699 # grams
        self.mass = mass - avg_tube_mass15 # N = 1 (in grams) 
        vol = (self.mass / density_water_25C) * 1000 # converts mL to uL
        super().__init__(name, deck_pos, loc, vol, conc)
       # 15mm diameter for 15 ml tube  -5: Five mL mark is 19 mm high for the base/noncylindrical protion of tube 

    def _update_height(self):
        diameter_15 = 14.0 # mm (V1 number = 14.4504)
        height_bottom_cylinder = 30.5  #mm
        height = ((self.vol - self.DEAD_VOL)/(math.pi*(diameter_15/2)**2))+height_bottom_cylinder
        self.height = height if height > height_bottom_cylinder else self.MIN_HEIGHT

    @property
    def disp_height(self):
        return self.height + 10 #mm

    @property
    def asp_height(self):
        tip_depth = 5
        return self.height - tip_depth
            
class Tube50000uL(Container):
    """
    Spcific tube with measurements taken to provide implementations of abstract methods
    INHERITED ATTRIBUTES
        str name, float vol, int deck_pos, str loc, float disp_height, float asp_height
    INHERITED METHODS
        _update_height void, update_vol(float del_vol) void,
    """

    DEAD_VOL = 5000
    MIN_HEIGHT = 1

    def __init__(self, name, deck_pos, loc, mass=13.3950, conc=1):
        density_water_25C = 0.9970479 # g/mL
        avg_tube_mass50 = 13.3950 # grams
        self.mass = mass - avg_tube_mass50 # N = 1 (in grams) 
        vol = (self.mass / density_water_25C) * 1000 # converts mL to uL
        super().__init__(name, deck_pos, loc, vol, conc)
       # 15mm diameter for 15 ml tube  -5: Five mL mark is 19 mm high for the base/noncylindrical protion of tube 
        
    def _update_height(self):
        diameter_50 = 26.50 # mm (V1 number = 26.7586)
        height_bottom_cylinder = 21 #mm
        height = ((self.vol - self.DEAD_VOL)/(math.pi*(diameter_50/2)**2)) + height_bottom_cylinder
        self.height = height if height > height_bottom_cylinder else self.MIN_HEIGHT

    @property
    def disp_height(self):
        return self.height + 10 #mm

    @property
    def asp_height(self):
        tip_depth = 5
        return self.height - tip_depth

class Tube2000uL(Container):
    """
    2000uL tube with measurements taken to provide implementations of abstract methods
    INHERITED ATTRIBUTES
         str name, float vol, int deck_pos, str loc, float disp_height, float asp_height
    INHERITED METHODS
        _update_height void, update_vol(float del_vol) void,
    """

    DEAD_VOL = 250 #uL
    MIN_HEIGHT = 1

    def __init__(self, name, deck_pos, loc, mass=1.4, conc=1):
        density_water_4C = 0.9998395 # g/mL
        avg_tube_mass2 =  1.4        # grams
        self.mass = mass - avg_tube_mass2 # N = 1 (in grams) 
        vol = (self.mass / density_water_4C) * 1000 # converts mL to uL
        super().__init__(name, deck_pos, loc, vol, conc)
           
    def _update_height(self):
        diameter_2 = 8.30 # mm
        height_bottom_cylinder = 10.5 #mm
        height = ((self.vol - self.DEAD_VOL)/(math.pi*(diameter_2/2)**2)) + height_bottom_cylinder
        self.height = height if height > height_bottom_cylinder else self.MIN_HEIGHT

    @property
    def disp_height(self):
        return self.height + 10 #mm

    @property
    def asp_height(self):
        tip_depth = 4.5 # mm
        return self.height - tip_depth

class Well96(Container):
    """
        a well in a 96 well plate
        INHERITED ATTRIBUTES
             str name, float vol, int deck_pos, str loc, float disp_height, float asp_height
        INHERITED CONSTANTS
            int DEAD_VOL TODO update DEAD_VOL from experimentation
        INHERITED METHODS
            _update_height void, update_vol(float del_vol) void,
    """

    MIN_HEIGHT = 1

    def __init__(self, name, deck_pos, loc, vol=0, conc=1):
        #vol is defaulted here because the well will probably start without anything in it
        super().__init__(name, deck_pos, loc, vol, conc)
           
    def _update_height(self):
        #this method is not needed for a well of such small size because we always aspirate
        #and dispense at the same heights
        self.height = None

    @property
    def disp_height(self):
        return 10 #mm

    @property
    def asp_height(self):
        return self.MIN_HEIGHT

#LABWARE
#TODO Labware was built with the assumption that once you ask for a bit of labware, you will use it
#if you don't want to pop, we must allow that functionality
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
    CONSTANTS
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
    #TODO better documentation of labware subclasses
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

    CONTAINERS_SERVICED = ['Tube50000uL', 'Tube20000uL', 'Tube2000uL']

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
        elif tube_capacity <= 20000:
            return 'Tube20000uL'
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
    OVERRIDEN CONSTANTS:
        list<str> CONTAINERS_SERVICED
    ATTRIBUTES:
        int current_well: the well number your on (NOT loc!)
    '''

    CONTAINERS_SERVICED = ['Well96']

    def __init__(self, labware, first_well, deck_pos):
        super().__init__(labware, deck_pos)
        #allow for none initialization
        n_rows = len(labware.columns()[0])
        col = first_well[:1]#alpha part
        row = first_well[1:]#numeric part
        self.current_well = (ord(col)-64)*n_rows #transform alpha num to num
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
    
    def get_container_type(self, loc):
        '''
        params:
            str loc: loc on the labware
        returns:
            str: the type of container
        '''
        return 'Well96'

#Robot
class OT2Controller():
    """
    The big kahuna. This class contains all the functions for controlling the robot
    ATTRIBUTES:
        str ip: IPv4 LAN address of this machine
        Dict<str, Container> containers: maps from a common name to a Container object
        Dict<str, Obj> tip_racks: maps from a common name to a opentrons tiprack labware object
        Dict<str, Obj> labware: maps from labware common names to opentrons labware objects. tip racks not included?
        Dict<str:Dict<str:Obj>>: JSON style dict. First key is the arm_pos second is the attribute
            'size' float: the size of this pipette in uL
            'last_used' str: the chem_name of the last chemical used. 'clean' is used to denote a
              clean pipette
        Opentrons...ProtocolContext protocol: the protocol object of this session
    """

    #Don't try to read this. Use an online json formatter 
    _LABWARE_TYPES = {"96_well_plate":{"opentrons_name":"corning_96_wellplate_360ul_flat","groups":["well_plate"],'definition_path':""},"24_well_plate":{"opentrons_name":"corning_24_wellplate_3.4ml_flat","groups":["well_plate"],'definition_path':""},"48_well_plate":{"opentrons_name":"corning_48_wellplate_1.6ml_flat","groups":["well_plate"],'definition_path':""},"tip_rack_20uL":{"opentrons_name":"opentrons_96_tiprack_20ul","groups":["tip_rack"],'definition_path':""},"tip_rack_300uL":{"opentrons_name":"opentrons_96_tiprack_300ul","groups":["tip_rack"],'definition_path':""},"tip_rack_1000uL":{"opentrons_name":"opentrons_96_tiprack_1000ul","groups":["tip_rack"],'definition_path':""},"tube_holder_10":{"opentrons_name":"opentrons_10_tuberack_falcon_4x50ml_6x15ml_conical","groups":["tube_holder"],'definition_path':""},"temp_mod_24_tube":{"opentrons_name":"opentrons_24_aluminumblock_generic_2ml_screwcap","groups":["tube_holder","temp_mod"],'definition_path':""},"platereader4":{"opentrons_name":"","groups":["well_plate","platereader"],"definition_path":"LabwareDefs/plate_reader_4.json"},"platereader7":{"opentrons_name":"","groups":["well_plate","platereader"],"definition_path":"LabwareDefs/plate_reader_7.json"},"platereader":{"opentrons_name":"","groups":["well_plate","platereader"]}}
    _PIPETTE_TYPES = {"300uL_pipette":{"opentrons_name":"p300_single_gen2"},"1000uL_pipette":{"opentrons_name":"p1000_single_gen2"},"20uL_pipette":{"opentrons_name":"p20_single_gen2"}}


    def __init__(self, simulate, using_temp_ctrl, temp, labware_df, instruments, reagents_df, ip, portal):
        '''
        params:
            bool simulate: if true, the robot will run in simulation mode only
            bool using_temp_ctrl: true if you want to use the temperature control module
            float temp: the temperature to keep the control module at.
            df labware_df:
                str name: the common name of the labware
                str first_usable: the first tip/well to use
                int deck_pos: the position on the deck of this labware
                str empty_list: the available slots for empty tubes format 'A1,B2,...' No specific
                  order
            Dict<str:str> instruments: keys are ['left', 'right'] corresponding to arm slots. vals
              are the pipette names filled in
            df reagents_df: info on reagents. columns from sheet. See excel specification
                
        postconditions:
            protocol has been initialzied
            containers and tip_racks have been created
            labware has been initialized
            CAUTION: the values of tip_racks and containers must be sent from the client.
              it is the client's responsibility to make sure that these are initialized prior
              to operating with them
        '''
        #DEBUG
        with open(os.path.join(CACHE_PATH,'robo_init_params.pkl'),'wb') as cache:
            dill.dump([simulate, using_temp_ctrl, temp, labware_df, instruments, reagents_df], cache)
        self.containers = {}
        self.pipettes = {}
        self.ip = ip
        self.portal = portal
        #like protocol.deck, but with custom labware wrappers
        self.lab_deck = np.full(12, None, dtype='object') #note first slot not used

        if simulate:
            # define version number and define protocol object
            self.protocol = opentrons.simulate.get_protocol_api('2.9')
        else:
            self.protocol = opentrons.execute.get_protocol_api('2.9')
            self.protocol.set_rail_lights(on = True)
            self.protocol.rail_lights_on 
        self.protocol.home() # Homes the pipette tip
        #empty list was in comma sep form for easy shipping. unpack now to list
        labware_df['empty_list'] = labware_df['empty_list'].apply(lambda x: x.split(',')
                if x else [])
        self._init_params()
        self._init_directories()
        self._init_labware(labware_df, using_temp_ctrl, temp)
        self._init_instruments(instruments, labware_df)
        self._init_containers(reagents_df)

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


    def _init_containers(self, reagents_df):
        '''
        params:
            df reagents_df: as passed to init
        Postconditions:
            the dictionary, self.containers, has been initialized to have name keys to container
              objects
        '''
        container_types = reagents_df['deck_pos'].apply(lambda d: self.lab_deck[d])
        container_types = reagents_df[['deck_pos','loc']].apply(lambda row: 
                self.lab_deck[row['deck_pos']].get_container_type(row['loc']),axis=1)
        container_types.name = 'container_type'

        for name, conc, loc, deck_pos, mass, container_type in reagents_df.join(container_types).itertuples():
            self.containers[name] = self._construct_container(container_type, name, deck_pos,loc, mass=mass, conc=conc)
    
    def _construct_container(self, container_type, name, deck_pos, loc, **kwargs):
        '''
        params:
            str container_type: the type of container you want to instantiate
            str name: the chemical name
            int deck_pos: labware position on deck
            str loc: the location on the labware
          **kwargs:
            float mass: the mass of the starting contents
            float conc: the concentration of the starting components
        returns:
            Container: a container object of the type you specified
        '''
        if container_type == 'Tube2000uL':
            return Tube2000uL(name, deck_pos, loc, **kwargs)
        elif container_type == 'Tube20000uL':
            return Tube20000uL(name, deck_pos, loc, **kwargs)
        elif container_type == 'Tube50000uL':
            return Tube50000uL(name, deck_pos, loc, **kwargs)
        elif container_type == 'Well96':
            #Note we don't yet have a way to specify volume since we assumed that we would
            #always be weighing in the input template. Future feature allows volume to be
            #specified in sheets making this last step more interesting
            return Well96(name, deck_pos, loc, **kwargs)
        else:
            raise Exception('Invalid container type')
       
    def _init_params(self):
        '''
        TODO: if this still just initializes speed when we're done, it should be named such
        '''
        self.protocol.max_speeds['X'] = 100
        self.protocol.max_speeds['Y'] = 100

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
        '''
        if using_temp_ctrl:
            temp_module = self.protocol.load_module('temperature module gen2', 3)
            temp_module.set_temperature(temp)
            opentrons_name = self._LABWARE_TYPES[name]['opentrons_name']
            labware = temp_module.load_labware(opentrons_name,label=name)
            #this will always be a tube holder
            self._add_to_deck(name, deck_pos, labware, empty_containers=empty_tubes)


    def _init_custom_labware(self, name, deck_pos, **kwargs):
        '''
        initializes custom built labware by reading from json
        initializes the labware_deck
        params:
            str name: the common name of the labware
            str deck_pos: the position on the deck for the labware
        kwargs:
            NOTE this is really here for compatibility since it's just one keyword that should
            always be passed. It's here in case we decide to use other types of labware in the
            future
            str first_well: the first available well in the labware
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
                list empty_containers<str>: the list of the empty locations on the labware
                str first_well: the first available well in the labware
        Postconditions:
            an entry has been added to the lab_deck
        '''
        if 'tube_holder' in self._LABWARE_TYPES[name]['groups']:
            self.lab_deck[deck_pos] = TubeHolder(labware, kwargs['empty_containers'], deck_pos)
        elif 'well_plate' in self._LABWARE_TYPES[name]['groups']:
            self.lab_deck[deck_pos] = WellPlate(labware, kwargs['first_well'], deck_pos)
        else:
            raise Exception("Sorry, Illegal Labware Option. Your labware is not a tube or plate")

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
            elif 'temp_mod' in self._LABWARE_TYPES[name]['definition_path']:
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
 
    def _exec_init_containers(self, product_df):
        '''
        used to initialize empty containers, which is useful before transfer steps to new chemicals
        especially if we have preferences for where those chemicals are put
        Params:
            df product_df: as generated in client init_robot
        Postconditions:
            every container has been initialized according to the parameters specified
        '''
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
                    raise Exception('No viable slots to put {}.'.format(chem_name))
                next_container_loc = viable.pop_next_well(vol=max_vol,container_type=req_container)
                if next_container_loc:
                    #that piece of labware has space for you
                    loc = next_container_loc
                    deck_pos = viable.deck_pos
                    container_type = viable.get_container_type(loc)
                i += 1
            self.containers[chem_name] = self._construct_container(container_type, 
                    chem_name, deck_pos, loc)


    #a dictionary to assign priorities to different labwares. Right now used only to prioritize
    #platereader when no other labware has been specified
    _exec_init_containers.priority = defaultdict(lambda: 100)
    _exec_init_containers.priority['platereader4'] = 1
    _exec_init_containers.priority['platereader7'] = 2

    def execute(self, command_type, cid, arguments):
        '''
        takes the packet type and payload of an Armchair packet, and executes the command
        params:
            str command_type: the type of packet to execute
            tuple<Obj> arguments: the arguments to this command 
              (generally passed as list so no *args)
        returns:
            int: 1=ready to recieve. 0=terminated
        Postconditions:
            the command has been executed
        '''
        if command_type == 'transfer':
            self._exec_tranfer(*arguments)
            self.portal.send_pack('ready', cid)
            return 1
        elif command_type == 'init_containers':
            self._exec_init_containers(arguments[0])
            self.portal.send_pack('ready', cid)
            return 1
        elif command_type == 'close':
            self._exec_close()
            return 0
        else:
            raise Exception("Unidenified command {}".format(pack_type))

    def _exec_tranfer(self, src, transfer_steps, callbacks):
        '''
        params:
            str src: the chem_name of the source well
            list<tuple<str,float>> transfer_steps: each element is a dst, vol pair
            list<str> callbacks: the ordered callbacks to perform after each transfer or None
        '''
        #we want to pick up new tip at the start
        new_tip=True
        for dst, vol in transfer_steps:
            self._transfer_step(src,dst,vol)
            new_tip=False #don't want to use a new tip_next_time
            if callbacks:
                for callback in callbacks:
                    #call the callback
                    pass
        return

    def _transfer_step(self, src, dst, vol):
        '''
        used to execute a single tranfer from src to dst. Handles things like selecting
        appropriately sized pipettes. dropping tip if it's a new chemical. If you need
        more than 1 step, will facilitate that
        '''
        #choose your pipette
        arm = self._get_preffered_pipette(vol)
        n_substeps = int(vol // self.pipettes[arm]['size']) + 1
        substep_vol = vol / n_substeps
        
        #if you need a new tip, get one 
        if src != self.pipettes[arm]['last_used'] and src != 'clean':
            self._get_new_tip(arm)

        #transfer the liquid in as many steps are necessary
        for i in range(n_substeps):
            self._liquid_transfer(src, dst, substep_vol, arm)
        return

    def _get_new_tip(self, arm):
        '''
        replaces the tip with a new one
        TODO: Michael found it necessary to test if has_tip. I don't think this is needed
          but revert to it if you run into trouble
        TODO: pickup tip on init
        TODO: Wrap in try for running out of tips
        '''
        pipette = self.pipettes[arm]['pipette']
        pipette.drop_tip()
        pipette.pick_up_tip()
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
        if vol < 50:
            preffered_size = 20.0
        elif vol < 600:
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

        if self.pipettes[larger_pipette]['size'] < preffered_size:
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
        '''
        self.protocol._commands.append('HEAD: {} : transfering {} to {}'.format(datetime.now().strftime('%d-%b-%Y %H:%M:%S:%f'), src, dst))
        pipette = self.pipettes[arm]['pipette']
        src_cont = self.containers[src] #the src container
        dst_cont = self.containers[dst] #the dst container
        #set aspiration height
        pipette.well_bottom_clearance.aspirate = self.containers[src].asp_height
        #aspirate(well_obj)
        pipette.aspirate(vol, self.lab_deck[src_cont.deck_pos].get_well(src_cont.loc))
        #update the vol of src
        src_cont.update_vol(-vol)
        #pipette is now dirty
        self.pipettes[arm]['last_used'] = src
        #touch tip
        pipette.touch_tip()
        #maybe move up if clipping
        #set dispense height 
        pipette.well_bottom_clearance.dispense = self.containers[dst].disp_height
        #dispense(well_obj)
        pipette.dispense(vol, self.lab_deck[dst_cont.deck_pos].get_well(dst_cont.loc))
        #update vol of dst
        dst_cont.update_vol(vol,src)
        #blowout
        for i in range(4):
            pipette.blow_out()
        #wiggle - touch tip (spin fast inside well)
        pipette.touch_tip(radius=0.3,speed=40)

    def dump_well_map(self):
        '''
        dumps the well_map to a file
        '''
        path=os.path.join(self.logs_p,'wellmap.tsv')
        names = self.containers.keys()
        locs = [self.containers[name].loc for name in names]
        deck_poses = [self.containers[name].deck_pos for name in names]
        vols = [self.containers[name].vol for name in names]
        def lookup_container_type(name):
            container = self.containers[name]
            labware = self.lab_deck[container.deck_pos]
            return labware.get_container_type(container.loc)
        container_types = [lookup_container_type(name) for name in names]
        well_map = pd.DataFrame({'chem_name':names, 'loc':locs, 'deck_pos':deck_poses, 
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

    def _exec_close(self):
        '''
        close the connection in a nice way
        '''
        print('<<eve>> initializing breakdown')
        #write logs
        self.dump_protocol_record()
        self.dump_well_histories()
        self.dump_well_map()
        #ship logs
        filenames = list(os.listdir(self.logs_p))
        port = 50001 #default port for ftp 
        self.send_files(port, filenames)
        #kill link
        print('<<eve>> shutting down')
        self.portal.send_pack('close')
        self.portal.close()

    def send_files(self,port,filenames):
        '''
        used to ship files back to server
        params:
            int port: the port number to ship the files out of
            list<str> filepaths: the filepaths to ship
        '''
        print('<<eve>> initializing filetransfer')
        filepaths = [os.path.join(self.logs_p, filename) for filename in filenames]
        self.portal.send_pack('sending_files', port, filenames)
        sock = socket.socket(socket.AF_INET)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        sock.bind((self.ip, port))
        sock.listen(5)
        client_sock, client_addr = sock.accept()
        for filepath in filepaths:
            with open(filepath,'rb') as local_file:
                client_sock.sendfile(local_file)
                client_sock.send(armchair.FTP_EOF)
            #wait until client has sent that they're ready to recieve again
        client_sock.close()
        sock.close()

def make_unique(s):
    '''
    makes every element in s unique by adding _1, _2, ...
    params:
        pd.Series s: a series of elements with some duplicates
    returns:
        pd.Series: s with any duplicates made unique by adding a count
    e.g.
    ['sloth', 'gorilla', 'sloth'] becomes ['sloth_1', 'gorilla', 'sloth_2']
    '''
    val_counts = s.value_counts()
    duplicates = val_counts.loc[val_counts > 1]
    def _get_new_name(name):
        #mini helper func for the apply
        if name in duplicates:
            i = duplicates[name]
            duplicates[name] -= 1
            return "{}_{}".format(name, i)
        else:
            return name
    return s.apply(_get_new_name)

#TESTING
def vol_calc(name):
    return rxn_df[name].sum() - rxn_df.loc[rxn_df['chemical_name'] == name, index].sum().sum()

def get_side_by_side_df(use_cache=False, labware_df=None, rxn_df=None, reagents_df=None, product_df=None, eve_logpath='Eve_Files'):
    '''
    This is for comparing the volumes, labwares, and containers
    params:
        df labware_df:
            str name: the common name of the labware
            str first_usable: the first tip/well to use
            int deck_pos: the position on the deck of this labware
            str empty_list: the available slots for empty tubes format 'A1,B2,...' No specific
              order
        df rxn_df: as from excel
        df reagents_df: info on reagents. columns from sheet. See excel specification
        df product_df:
            INDEX
            str chem_name
            COLS
            str labware: requested labware
            float max_vol: the maximum volume that this container will ever hold
        str eve_logpath: the path to the eve's logfiles
    returns
        df
            INDEX
            chemical_name: the containers name
            COLS: symmetric. Theoretical are suffixed _t
            str deck_pos: position on deck
            float vol: the volume in the container
            list<tuple<str, float>> history: the chem_name paired with the amount or
              keyword 'aspirate' and vol
    '''
    if use_cache:
        with open(os.path.join(CACHE_PATH,'robo_init_params.pkl'),'rb') as robo_cache:
            arguments = dill.load(robo_cache)
            labware_df = arguments[3]
            reagents_df = arguments[5]
        rxn_df, product_dict = load_rxn_table(None,None) #USE_CACHE must be active
        product_df = construct_product_df(rxn_df, product_dict)
        theoretical_df = build_theoretical_df(labware_df, rxn_df, reagents_df, product_df)
        result_df = pd.read_csv('Eve_Files/wellmap.tsv', sep='\t').set_index('chem_name')
        sbs = result_df.join(theoretical_df, rsuffix='_t') #side by side
        return sbs

def build_theoretical_df(labware_df, rxn_df, reagent_df, product_df):
    '''
    params:
        NOTE: As passed to get_side_by_side_df
        df labware_df: info on labware
        df rxn_df: rxn protocol
        df reagent_df: info on reagents
        df product_df: has the labware requested for product
    returns:
        df
            INDEX
            chemical_name: the containers name
            COLS
            str deck_pos: position on deck
            float vol: the volume in the container
    '''
    labware_df = labware_df.set_index('name').rename(index={'platereader7':'platereader',
            'platereader4':'platereader'}) #converting to dict like
    def get_deck_pos(labware):
        if labware:
            deck_pos = labware_df.loc[labware,'deck_pos']
            if isinstance(deck_pos,np.int64):
                return [deck_pos]
            else:
                #for platereader with two indices
                return deck_pos.to_list()
        else:
            return 'any'
    product_df['deck_pos'] = product_df['labware'].apply(get_deck_pos)
    product_df['vol'] = [vol_calc(name,rxn_df) for name in product_df.index]
    product_df['container']
    product_df['loc'] = 'any'
    product_df.replace('','any', inplace=True)
    reagent_df['deck_pos'] = reagent_df['deck_pos'].apply(lambda x: [x])
    reagent_df['vol'] = 'any' #I'm not checking this because it's harder to check, and works fine
    reagent_df['container'] = 'any' #actually fixed, but checked by combo deck_pos and loc
    theoretical_df = pd.concat((reagent_df.loc[:,['loc', 'deck_pos','vol','container']], product_df.loc[:,['loc', 'deck_pos','vol','container']]))
    return theoretical_df

def vol_calc(name, rxn_df):
    '''
    params:
        str name: chem_name
        df rxn_df: from excel
    returns:
        volume at end in that name
    '''
    dispenses = rxn_df[name].sum()
    aspirations = rxn_df.loc[(rxn_df['op']=='transfer') &\
            (rxn_df['chemical_name'] == name),products(rxn_df)].sum().sum()
    return dispenses - aspirations

def products(rxn_df):
    '''
    handy accessor method to get the products of rxn_df
    Preconditions:
        reagent is the first column before the products, 'chemical_name' is the last col
    params:
        df rxn_df: as in excel
    returns:
        index: the products
    '''
    return rxn_df.loc[:,'reagent':'chemical_name'].drop(columns=['chemical_name', 'reagent']).columns
def is_valid_sbs(row):
    '''
    params:
        pd.Series row: a row of a sbs dataframe:
    returns:
        Bool: True if it is a valid row
    '''
    if row['deck_pos_t'] != 'any' and row['deck_pos'] not in row['deck_pos_t']:
        print('deck_pos_error:')
        print(row.to_frame().T)
        print()
        return False
    if row['vol_t'] != 'any' and not math.isclose(row['vol'],row['vol_t'], abs_tol=1e9):
        print('volume error:')
        print(row.to_frame().T)
        print()
        return False
    if row['container_t'] != 'any' and not row['container'] == row['container_t']:
        print('container error:')
        print(row.to_frame().T)
        print()
        return False
    if row['loc_t'] != 'any' and not row['loc'] == row['loc_t']:
        print('loc error:')
        print(row.to_frame().T)
        print()
        return False
    return True

def has_correct_contents(rxn_df=None, use_cache=True, eve_logpath='Eve_Files'):
    '''
    tests to ensure that the contents of each container is correct
    note does not work for dilutions, and does not check reagents
    params:
        df rxn_df: from excel
        bool use_cache: True if data is cached
        str eve_logpath: the path to the eve logfiles
    Postconditions:
        if a difference was found it will be displayed,
        if no differences are found, a friendly print message will be displayed
    '''
    if use_cache:
        rxn_df, product_dict = load_rxn_table(None,None) #USE_CACHE must be active
    history = pd.read_csv(os.path.join(eve_logpath, 'well_history.tsv'),na_filter=False,sep='\t').rename(columns={'chemical':'chem_name'})
    disp_hist = history.loc[history['chem_name'].astype(bool)]
    contents = disp_hist.groupby(['container','chem_name']).sum()
    products = rxn_df.loc[:,'reagent':'chemical_name'].drop(columns=['reagent','chemical_name']).columns
    theoretical_his_list = []
    for _, row in rxn_df.loc[rxn_df['op']=='transfer'].iterrows():
        for product in products:
            theoretical_his_list.append((product, row[product], row['chemical_name']))
    theoretical_his = pd.DataFrame(theoretical_his_list, columns=['container', 'vol', 'chem_name'])
    theoretical_contents = theoretical_his.groupby(['container','chem_name']).sum()
    theoretical_contents = theoretical_contents.loc[~theoretical_contents['vol'].apply(lambda x:\
            math.isclose(x,0))]
    sbs = theoretical_contents.join(contents, how='left',lsuffix='_t')
    sbs['flag'] = (sbs.apply(lambda r: math.isclose(r['vol_t'], r['vol']),axis=1))
    if not sbs.loc[~sbs['flag']].empty:
        print('found some invalid contents. Displaying rows')
        container_index = sbs.loc[~sbs['flag']].index.get_level_values('container')
        print(sbs.loc[container_index])
    else:
        print('Well done! Product have correct ratios of reagents')
