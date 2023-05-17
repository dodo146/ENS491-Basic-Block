# Helper functions for static analyzer

from glob import glob
import imp
import string
from collections import deque

from shared import BASIC_BLOCKS

def is_hex(s):
    k = s
    if k == "":
        return False
    else:
        if k[:2] == "0x":
            k = k[2:]
        return all(c in string.hexdigits for c in k)

def hexLeadingZeroEreaser(hexText):
    result = ''
    try:
        if(hexText!= None):
            result = hex(int(hexText,0))
    except:
        print('Error in hexLeadingZeroEreaser ')
    return result

def get_block_by_address(address: str):
    for block in BASIC_BLOCKS:
        if block.start_address == address:
            return block
    return None

def find_instructions(instruction: str):
    res = r.cmd('/a %s' % instruction)
    list = []
    if (res != ""):
        splitted = res.split('\n')[:-1]
        [list.append(x.split(' ')[0]) for x in splitted]
    return list

def get_bb_address(addr):  # take addr of an instruction and find in which block this instruction exists.
    res = r.cmd('/ab %s' % addr)
    if (res != ""):
        splitted = res.split('\n')[:-1]
        for line in splitted:
            if 'addr' in line:
                return line.split(": ")[1]

def set_rdtsc_exist(block_list):
    rdtsc_list = find_instructions("rdtsc")
    print(rdtsc_list)
    for rdtsc_addr in rdtsc_list:
        bb_address = get_bb_address(rdtsc_addr)
        for block in block_list:
            if block.start_address == bb_address:
                block.rdtsc_flag = True
                block.rdtsc_list.append(rdtsc_addr)

def get_instr_size(address):
    return 1

#the function will convert all hex fields to standartformat like 0x00002457 to 0x2457 
def convertAllHexBasicBlockFieldsToStandardFormat(Basic_Blocks):
    for block in Basic_Blocks:
        block.start_address = hexLeadingZeroEreaser(block.start_address)
        block.end_address = hexLeadingZeroEreaser(block.end_address)
        if(block.jump_false_flag == True):
            block.jump_false_address = hexLeadingZeroEreaser(block.jump_false_address)
        if(block.jump_true_flag == True):
            block.jump_true_address = hexLeadingZeroEreaser(block.jump_true_address)

def printBasicBlocks(basicBlocks):
    for k in basicBlocks:
        print("start_address:{} | end_address:{} | jump_t_flag:{} | jump_t_address:{} |\
            jump_f_flag:{} | jump_f_address:{} | fake_xrefs:{} | is_function_call:{} | call_jump_address:{} | calls:{} | xrefs_flag:{} | xrefs:{} |\
            fcns_flag:{} | fcns:{} | size:{} | index:{}\n\n".format(
            k.start_address, k.end_address, k.jump_true_flag, k.jump_true_address,
            k.jump_false_flag, k.jump_false_address, k.fake_xrefs, k.calls_flag, k.call_jump_address, k.calls, k.xrefs_flag, k.xrefs,
            k.fcns_flag, k.fcns, k.size, k.index))

#deprived
#set Approximate Instruction Counts to size field of blocks. 3 address differences assumed approximately 1 instruction. 
def setApproximateInstructionCounts(basic_blocks):
    for block in basic_blocks:
        address_difference = int(block.end_address,0) - int(block.start_address,0)
        if(address_difference % 3 == 0):
            block.size = address_difference // 3
        else:
            block.size = (address_difference // 3) + 1

def setNumberOfBytesBetweenAddresses(start_address,end_address):
    return int(end_address,0)- int(start_address,0)

