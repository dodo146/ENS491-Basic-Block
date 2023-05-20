
#!/usr/bin/python3

from cmath import exp
import os
import r2pipe
import json
from tqdm import tqdm  # !! pip install tqdm -> nice library for progress bar
from utils import *
from shared import *
import networkx as nx
import sys

#TODO
#find the graph fonksiyonu doğru çalışmıyor düzelt


list_of_function_blocks = []


global_block_dict = {}

new_block_start_position = None

stop_splitting = False

def find_function_blocks():
    result = callJsonFromRadare("aflqj")
    result = result[1:len(result) -2]
    if "]" in result:
        result = result.replace("]","")
    result = result.split(",")
    for r in result:
        list_of_function_blocks.append(hex(int(r)))

def only_function_blocks():
    temp = []
    for block in BASIC_BLOCKS:
        if block.start_address in list_of_function_blocks:
            temp.append(block)
    
    return temp

class Abl_Basic_Block(object):
    def __init__(self, start_address):
        self.start_address = start_address

        # Will be add later
        self.end_address = None
        # this is the address that block jumps if the
        # condition true
        self.jump_true_address = None
        # this is the address that block jumps otherwise
        self.jump_false_address = None
        # size of the basic block
        self.size = None
        # Cross refs of the block as an array
        self.xrefs = set()
        # Func of the block as an array
        self.call_inst_address = None
        
        self.instr = []

        self.fcns = []
        #
        self.calls = []

        self.ninstr = None

        self.start_block = None
        # if the block has jump this flag will be true.
        self.jump_true_flag = False
        # if the block has only true jump, this flag will be false.
        self.jump_false_flag = False
        # if the block has cross refs this flag will be true.
        self.xrefs_flag = False
        # if the block calls functions this flag will be true.
        self.fcns_flag = False
        #IF THIS BLOCK IS A CALL BLOCK
        self.calls_flag = False  
        #If this block is a call the jump address will be seen in this field
        self.call_jump_address = None
        #If a block is splitted and appended at the end of basic blocks,this will be True
        self.first_splitted = False

        self.fake_xrefs = set()

    def __hash__(self) -> int:
        return hash(repr(self))

    def __getattr__(self, __name: str):
        return object.__getattr__(self,__name)

    def __getitem__(self,key):
        return self.__dict__[key]
           
    def __eq__(self, __o: object) -> bool:
        return hasattr(__o, "start_address") and self.start_address == __o.start_address
    
    def __repr__(self) -> str:
        return f"{self.start_address}"

    def __str__(self) -> str:
        return f"{self.start_address}"


def assign_blocks_objects():
    for block in BASIC_BLOCKS:
        if block.jump_true_address is not None:
            block.jump_true_address = global_block_dict[block.jump_true_address]
        if block.jump_false_address is not None:
            block.jump_false_address = global_block_dict[block.jump_false_address]
    

def callJsonFromRadare(command):
    allJsonRadareResults = []
    for i in range(10):
        resultFromRadare = r.cmd(command)
        allJsonRadareResults.append(resultFromRadare)
        if(len(allJsonRadareResults)>2 and (allJsonRadareResults[-1]==allJsonRadareResults[-2])):
            return resultFromRadare
    else:
        print("ERRORJSON: Some problems occured in callJsonFromRadare.Command is {}".format(command))
        return ''



def parse_abl_result(file: str):
    # get Json object
    blocksJson = json.loads(file)

    # traverse the blocks for all json object
    for idx in tqdm(blocksJson["blocks"], desc="Parsing Ablj Results..."):
        # for idx in blocksJson["blocks"]:
        startAdress = idx["addr"]
        bsc = Abl_Basic_Block(startAdress)
        sizeBlock = idx["size"]
        bsc.size = sizeBlock
        intEndAddress = hex(int(startAdress, 16) + sizeBlock)
        bsc.end_address = intEndAddress
        fill_instruction(bsc)
        if 'jump' in idx:
            bsc.jump_true_flag = True
            bsc.jump_true_address = hex(idx["jump"])
        if 'fail' in idx:
            bsc.jump_false_flag = True
            bsc.jump_false_address = hex(idx["fail"])
        if 'xrefs' in idx:
            bsc.xrefs_flag = True
            bsc.xrefs = set(idx["xrefs"])
            # #print(bsc.xrefs,"%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%")
        if 'fcns' in idx:
            bsc.fcns_flag = True
            bsc.fcns = []
            for f in idx["fcns"]:
                bsc.fcns.append(hex(f))
        if 'ninstr' in idx:
            bsc.ninstr = idx["ninstr"]
        if 'calls' in idx:
            bsc.calls_flag = True
            for i in idx['calls']:
                bsc.calls.append(i)
        global_block_dict[bsc.start_address] = bsc
        BASIC_BLOCKS.append(bsc)


def fill_instruction(block):
    r.cmd(f"s {block.start_address}")
    res = callJsonFromRadare("afbij")
    result = json.loads(res)
    block.instr = result['instrs']
    for ind,instr in enumerate(block.instr):
        block.instr[ind] = hex(instr)

        
#   This function takes a block and splits it into several blocks if CALL instruction(s) exist.
#   At the termination of this function, it is provided that all CALLs are separate blocks.
#   calls_flag = true if the block is a CALL block. 
#   If calls_flag = true, you can go to the address of that function by calls[0] which returns the address of the function
#   If calls_flag = false, you dont need to do anything, that basic block is a simple basic block in which no CALL instruction exist.
#   BB = [mov , mov , call, add, sub, j] --> RESULT = [mov,mov] --> [call] --> [add,sub,j] 
#   calls maybe empty (we are doing static analysis, we cant resolve address)

#Find the actual graph that the block is part of
def find_the_graph(block):
    return global_function_dict[block.start_block]


def find_after_call_instruction(block,address):
    #finds the address of the instruction after the call
    after_call_address = None
    if len(block.instr) == 0:
        after_call_address = block.end_address
    else:
        for ind,instr in enumerate(block.instr):
            if instr == address:
                if ind + 1 == block.ninstr:
                    after_call_address = block.end_address
                    break
                else:
                    after_call_address = block.instr[ind + 1]
                    break
    return after_call_address

def split_call(block: Abl_Basic_Block, from_next, jump_true_addr,jump_false_addr):
    print(block.start_address)
    r.cmd("e search.from = %s;" % block.start_address)
    r.cmd("e search.to = %s;" % hex(int(block.start_address,16) + block.size))
    global new_block_start_position,stop_splitting
    # find instruction in given address range. then get result as string.
    result = callJsonFromRadare("/am call")
    block.calls_flag = False
    block.calls = []
    if (from_next):
        BASIC_BLOCKS.append(block)

    if new_block_start_position is not None:
        if block.start_address == new_block_start_position.start_address:
            print("From now on there are splitted blocks. Stop splitting")
            stop_splitting = True
            return  

    if (result != ""):
        graph = find_the_graph(block)
        result = result.split('\n')[:-1]
        ress = None  # result[0] = the address of the CALL instruction. result[3] = the address that the CALL goes.
        for res in result:
            res = res.split(' ')
            if "\r" in res[-1]:
                res[-1] = res[-1].replace("\r","")
            if "\n" in res[-1]:
                res[-1] = res[-1].replace("\n","")
            if res[1] == "call" and res[3] == "call":
                ress = res
                break
        if ress is not None:
            result = ress
        else:
            result = [""]
        result[0] = hexLeadingZeroEreaser(result[0])
        call_address = result[0]
        if (is_hex(result[-1]) == True):        
            jump_addr = global_block_dict[result[-1]]
            # Construct the block which contains only the CALL
            call_block = Abl_Basic_Block(result[0])
            #call instructiondan bir sonraki instructionın adresini bul.O adres senin end_addresindir.
            call_block.end_address = find_after_call_instruction(block,call_address)
            call_block.size = int(call_block.end_address, 16) - int(call_block.start_address, 16)
            call_block.calls_flag = True
            call_block.calls.append(jump_addr)
            call_block.instr = [call_address]
            call_block.ninstr = 1
            call_block.call_inst_address = call_address
            call_block.call_jump_address = jump_addr
            call_block.start_block = block.start_block
            if new_block_start_position == None:
                new_block_start_position = call_block
        
            # CALL instruction is the only instruction in this block.
            if int(result[0], 16) == int(block.start_address, 16) and block.ninstr == 1:
                
                block.calls_flag = True
                block.fake_xrefs = block.fake_xrefs.union(block.xrefs)
                block.calls.append(jump_addr)
                return  # We do not need to do anything, it is already separated.

            # CALL is the last instruction. Modify the current block.
            elif block.instr[-1] == call_block.start_address:
                call_block.jump_false_address = block.jump_false_address
                call_block.jump_true_address = block.jump_true_address
                call_block.jump_true_flag = block.jump_true_flag
                call_block.jump_false_flag = block.jump_false_flag

                call_block.fake_xrefs = call_block.fake_xrefs.union(block.fake_xrefs)
                call_block.fake_xrefs = call_block.fake_xrefs.union(block.xrefs)
                call_block.call_jump_address = jump_addr

                block.end_address = block.instr[-1]
                block.instr = block.instr[0:-1]
                block.ninstr = len(block.instr)
                block.jump_true_flag = True
                block.jump_true_address = call_block # block will jump to call block. #direk call_blok yap ve jump true ve false
                #adresleri liste yap => listedeki sıra jump sırasına göre olacak
                block.size = int(block.end_address, 16) - int(block.start_address, 16)
                block.jump_false_address = None
                
                #update its predecessors in the graph
                pred_graph = find_the_graph(block)
                if pred_graph == graph:
                    update_predecessors(block,graph)
                else:
                    update_predecessors(block,pred_graph)

                #update the current neighbors
                delete_neigbour_nodes = list(dict(graph.adj[block].items()).keys())
                for neigbour in delete_neigbour_nodes:
                    graph.remove_edge(block,neigbour)

                graph.add_edge(block,call_block)
                if call_block.jump_true_flag == False and call_block.jump_false_flag == False:
                    graph.add_node(call_block)
                else:
                    if call_block.jump_true_address is not None:
                        graph.add_edge(call_block,call_block.jump_true_address)
                    if call_block.jump_false_address is not None:
                        graph.add_edge(call_block,call_block.jump_false_address)


                global_block_dict[call_block.start_address] = call_block
                BASIC_BLOCKS.append(call_block)

                #print("Block splitted")


            # CALL instruction is the first instruction
            elif call_block.start_address == block.start_address:  # CALL is the 1st instruction. No need to create a call_block.
                # Just create a next block and modify the block and bind next block and block accordingly.
                next_block = Abl_Basic_Block(call_block.end_address)
                next_block.end_address = block.end_address
                next_block.size = int(next_block.end_address, 16) - int(next_block.start_address, 16)
                next_block.jump_false_address = block.jump_false_address
                next_block.jump_true_address = block.jump_true_address
                next_block.jump_false_flag = block.jump_false_flag
                next_block.jump_true_flag = block.jump_true_flag

                next_block.fake_xrefs = next_block.fake_xrefs.union(block.fake_xrefs)
                next_block.fake_xrefs = next_block.fake_xrefs.union(block.xrefs)

                index = block.instr.index(call_address)
                next_block.instr = block.instr[index+1:]
                next_block.ninstr = len(next_block.instr)

                block.end_address = call_block.end_address
                block.call_inst_address = call_block.call_inst_address
                block.call_jump_address = call_block.call_jump_address
                block.calls = call_block.calls
                block.fcns = call_block.fcns
                block.fcns_flag = call_block.fcns
                block.fake_xrefs = call_block.fake_xrefs
                block.xrefs = call_block.xrefs
                block.instr = call_block.instr
                block.ninstr = call_block.ninstr
                block.size = call_block.size
                block.first_splitted = call_block.first_splitted
                block.start_block = call_block.start_block
                block.calls_flag = True
                block.jump_true_address = next_block
                block.jump_true_flag = True
                block.jump_false_address = None
                block.jump_false_flag = False

                #update its predecessors in the graph
                pred_graph = find_the_graph(block)
                if pred_graph == graph:
                    update_predecessors(block,graph)
                else:
                    update_predecessors(block,pred_graph)

                #update the current graph's neigbours
                delete_neigbour_nodes = list(dict(graph.adj[block].items()).keys())
                for neigbour in delete_neigbour_nodes:
                    graph.remove_edge(block,neigbour)

                graph.add_edge(block,next_block)
                if next_block.jump_true_flag == False and next_block.jump_false_flag == False:
                    graph.add_node(block)
                else:
                    if next_block.jump_true_address is not None:
                        graph.add_edge(next_block,next_block.jump_true_address)
                    if next_block.jump_false_address is not None:
                        graph.add_edge(next_block,next_block.jump_false_address)
                
                next_block.start_block = block.start_block
                global_block_dict[next_block.start_address] = next_block
                ind = BASIC_BLOCKS.index(block)
                BASIC_BLOCKS[ind] = block

                print("Current block splitted.Looking for other calls...")
                # Keep searching for further calls in the next block
                split_call(next_block, 1,next_block.jump_true_address,next_block.jump_false_address) 

            # GENERAL CASE. CALL is at the middle of somewhere.
            else:
                index = block.instr.index(call_address)
                next_block = Abl_Basic_Block(call_block.end_address)  # Next block will be after the call_block which is only 1 instruction
                next_block.end_address = block.end_address
                next_block.jump_true_address = block.jump_true_address
                next_block.jump_false_address = block.jump_false_address
                next_block.jump_true_flag = block.jump_true_flag
                next_block.jump_false_flag = block.jump_false_flag

                next_block.fake_xrefs = next_block.fake_xrefs.union(block.fake_xrefs)
                next_block.fake_xrefs = next_block.fake_xrefs.union(block.xrefs)

                next_block.size = int(next_block.end_address, 16) - int(next_block.start_address, 16)
                next_block.instr = block.instr[index + 1:]
                next_block.ninstr = len(next_block.instr)

                block.calls_flag = False
                block.end_address = call_block.start_address
                block.jump_true_address = call_block
                block.jump_true_flag = True
                block.size = int(call_block.start_address, 16) - int(block.start_address, 16)
                block.jump_false_flag = False
                block.jump_false_address = None
                block.instr = block.instr[0:index]
                block.ninstr = len(block.instr)

                call_block.jump_true_address = next_block
                call_block.jump_true_flag = True

                call_block.fake_xrefs = call_block.fake_xrefs.union(block.fake_xrefs)
                call_block.fake_xrefs = call_block.fake_xrefs.union(block.xrefs)

                #update its predecessors in the graph
                pred_graph = find_the_graph(block)
                if pred_graph == graph:
                    update_predecessors(block,graph)
                else:
                    update_predecessors(block,pred_graph)
                
                #update the neighbors
                delete_neigbour_nodes = list(dict(graph.adj[block].items()).keys())
                for neigbour in delete_neigbour_nodes:
                    graph.remove_edge(block,neigbour)

                graph.add_edge(block,call_block)
                if call_block.jump_true_flag == False and call_block.jump_false_flag == False:
                    graph.add_node(call_block)
                else:
                    if call_block.jump_true_address is not None:
                        graph.add_edge(call_block,call_block.jump_true_address)
                    if call_block.jump_false_address is not None:
                        graph.add_edge(call_block,call_block.jump_false_address)
                
                if next_block.jump_true_address is not None:
                        graph.add_edge(next_block,next_block.jump_true_address)
                if next_block.jump_false_address is not None:
                    graph.add_edge(next_block,next_block.jump_false_address)

                BASIC_BLOCKS.append(call_block)
                next_block.start_block = block.start_block

                global_block_dict[call_block.start_address] = call_block
                global_block_dict[next_block.start_address] = next_block
                print("Current block splitted.Looking for other calls...")
                split_call(next_block, 1,next_block.jump_true_address,next_block.jump_false_address)  # Keep searching for further calls in the next block.

        else:
            #print("There is a CALL but address cannot be resolved")
            pass
    else:
        #print("There are no call instructions")
        pass


def update_predecessors(block,graph):
    #update its predecessors in the graph
        pred_list = list(graph.predecessors(block))
        print(pred_list)
        if len(pred_list) == 0:
            print(f"This block {block} has no predecessors.")
            pass
        else:
            if len(pred_list) == 1:
                pred = pred_list[0]                   
                delete_neigbour_nodes = list(dict(graph.adj[pred].items()).keys())
                for n in delete_neigbour_nodes:
                    if n.start_address == block.start_address:
                        graph.remove_edge(pred,n)
                graph.add_edge(pred,block)
            else:
                print(f"This block {block} has more than one predecessors. Do something")
                for pred in pred_list:      
                    delete_neigbour_nodes = list(dict(graph.adj[pred].items()).keys())
                    for n in delete_neigbour_nodes:
                        if n.start_address == block.start_address:
                            graph.remove_edge(pred,n)
                    graph.add_edge(pred,block)



def fill_xref_fields():
    # iterate each block (tqdm for progress bar)
    for block in tqdm(BASIC_BLOCKS, desc="Filling xrefs..."):
        # for block in BASIC_BLOCKS:
        block_start_address = block.start_address
        #Since r2 pipe do not return correct json output all the time, we will call afbj 50 times until it return expected output. 
        for i in range(50):
            try:
                #testRadareCmd = r.cmd("s main")
                afb_result = callJsonFromRadare("afbj {}".format(block_start_address))
                #afb_result = r.cmd("afbj {}".format(block_start_address))
                afb_json = json.loads(afb_result)
                function_address_int = afb_json[0]["addr"]
                function_address_hex = hex(function_address_int)
                break
            except:
                unUsedVar = 1
                print("INFO: In fill_xref_fields radare2 returned unexpected output in iteration ",i)
        else:
            print("ERRORJSON: In fill_xref_fields radare2 returned unexpected output 50 timesin JSON1. Program will exit.")
            print(afb_result)
            exit(1)
            
        #Since r2 pipe do not return correct json output all the time, we will call afbj 50 times until it return expected output. 
        for i in range(50):
            try:
                #testRadareCmd = r.cmd("s main")
                axt_result = callJsonFromRadare("axtj {}".format(function_address_hex))
                #axt_result = r.cmd("axtj {}".format(function_address_hex))
                axt_json = json.loads(axt_result)
                # #print("\n BLOCK ADDR: {} -----------------<".format(block_start_address))
                for xref in axt_json:
                    if xref['type'] == 'CALL':
                        xref_address_int = int(xref['from'])
                        block.fake_xrefs.add(xref_address_int)
                break
            except:
                unUsedVar = 1
                print("INFO: In fill_xref_fields radare2 returned unexpected output in iteration ",i)
        else:
            print("ERRORJSON: In fill_xref_fields radare2 returned unexpected output 50 times in JSON2. Program will exit.")
            print(axt_result)
            exit(1)
        
        for i in range(50):
            try:
                #testRadareCmd = r.cmd("s main")
                axt_result = callJsonFromRadare("axtj {}".format(block_start_address))
                #axt_result = r.cmd("axtj {}".format(block_start_address))
                axt_json = json.loads(axt_result)
                block.xrefs = set()
                for xref in axt_json:
                    if xref['type'] == 'CALL':
                        xref_address_int = int(xref['from'])
                        block.xrefs.add(xref_address_int)
                break
            except:
                unUsedVar = 1
                print("INFO: In fill_xref_fields radare2 returned unexpected output in iteration ",i)
        else:
            print("ERRORJSON: In fill_xref_fields radare2 returned unexpected output 50 times in JSON3. Program will exit.")
            print(axt_result)
            exit(1)
        

def parse_afb_result(block):
    blocks = []
    r.cmd(f"s {block.start_address}")
    res = callJsonFromRadare("afbj")
    result = json.loads(res)
    for bl in result:
        obj = hex(bl['addr'])
        blocks.append(global_block_dict[obj])
    return blocks

def create_graph_on_function_blocks():
    g = nx.DiGraph()
    for block in BASIC_BLOCKS:
        if block in function_blocks: 
            jump_true_ind = False
            jump_false_ind = False

            a_list = list(global_function_dict.values())
                
            if len(a_list) == 0:
                graph = nx.DiGraph()
            else:
                graph = list(global_function_dict.values())[-1]

            if block in list(graph.nodes):
                continue
            else:
                cfg_nodes = parse_afb_result(block)
                for fblock in cfg_nodes:
                    fblock.start_block = block
                    if fblock.jump_true_address is not None:
                        g.add_edge(fblock,fblock.jump_true_address)
                        jump_true_ind = True
                    if fblock.jump_false_address is not None:
                        g.add_edge(fblock,fblock.jump_false_address)
                        jump_false_ind = True
                    
                if jump_true_ind == False and jump_false_ind == False:
                    g.add_node(fblock)


                # leaves = [v for v,d in g.out_degree() if d == 0]
                # g.graph["last_nodes"] = leaves
                copy_g = g.copy()
                global_function_dict[block] = copy_g
                g.clear()
        else:
            continue


def change_address_format(address,k):
    int_binary_address = int(address,16)
    binary_address = bin(int_binary_address) #'0b10001011001001'
    binary_address = binary_address[:len(binary_address) - k ]
    new_address = hex(int(binary_address,2))
    return new_address

def select_start_vertex(graph,address):
    addresses = list(graph.keys())
    addresses = [element.start_address for element in addresses]
    if address not in addresses:
        return ""
    else:
        return address




def main(filename,subpath_length,starting_point):
    global r
    global FILE
    FILE = filename
    global global_function_dict
    global_function_dict = {}
    global function_blocks
    global new_block_start_position

     
    r = r2pipe.open(FILE)
    name = FILE.split('/')[-1]
    print("FileName: {} ".format(name))

    # Analyze all
    print("########### ANALYZING THE FILE #################")
    r.cmd('aaa;')
    abl_result = callJsonFromRadare('ablj')

    while abl_result == '':
        abl_result = callJsonFromRadare.cmd('ablj')

    parse_abl_result(abl_result)

    assign_blocks_objects()

    # print("########### FILLING XREF FIELDS ###################")
    # fill_xref_fields()

    r.cmd("aflsa")
    find_function_blocks()

    function_blocks = only_function_blocks()
    create_graph_on_function_blocks()

    print("########### {} BASIC BLOCKS CREATED ###########".format(len(BASIC_BLOCKS)))
    print("########### SPLITTING CALLS ###################")

    for block in BASIC_BLOCKS:
        split_call(block, 0,None,None)
        if stop_splitting:
            break



    valid_address = False
    print("\n\n")    
    target_count = subpath_length

    while(not valid_address):
        start_vertex = starting_point
        result_address = select_start_vertex(global_function_dict,start_vertex)
        if result_address == "":
            print("This is not a valid address. Please try again.")
        else:
            valid_address = True
                
    vertex = global_block_dict[result_address]
    graph = global_function_dict[vertex]
    result_list = dfs_search(graph,vertex,target_count)
    return result_list
    
#This function is for searching the graph and taking possible subpaths including calls
def dfs_search(graph,vertex,cutoff_length,path=[]):
    path.append(vertex)
    current_path = path.copy()
    if cutoff_length == 0:
        yield path
        return
    if vertex.calls_flag == True:
        call_graph = find_the_graph(vertex.call_jump_address)
        yield from dfs_search(call_graph,vertex.call_jump_address,cutoff_length-1,path)
        path = current_path.copy()
    for neighbour in graph.adj[vertex]:
        yield from dfs_search(graph,neighbour,cutoff_length-1,path)
        path = current_path.copy()
    return

def is_convertible_to_int(string):
    try:
        int(string)
        return True
    except ValueError:
        return False

if __name__ == "__main__":
    print("Start#######################################Start")
    target_count = None
    address = None
    #filename = "C:/Users/digde/source/repos/Projects/Visual Studio 2019 projets/test/x64/Release/test.exe"
    filename = None
    args = sys.argv
    for arg in args[1:]:
        if os.path.exists(arg):
            #it is a path
            filename = arg
        elif is_convertible_to_int(arg):
            #it is target count
            target_count = int(arg)
        elif type(arg) == str:
            # it is address
            address = arg
        else:
            print("Given argument is invalid.Please check your argument again!.Exiting...")
            exit(1)

    #windows için file pathleri
    #filename = "C:/Users/digde/VS Code projects/C++ Codes/Visual Studio 2019 projets/WordSearch/Release/WordSearch.exe"
    result = main(filename,target_count,address)
    for path in result:
        print(path)
        # for node in path:
        #     changed_address = change_address_format(str(node),8)
        #     print(changed_address)

    print("End########################################End")