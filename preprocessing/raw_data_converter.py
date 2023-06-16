import struct
import copy
import math
import sys
import functools


"""
this is a list of 3-tuples. Each tuple contains (in this order)
1. (int)     the onnx representation of the datatype (found in https://github.com/onnx/onnx/blob/main/onnx/onnx.proto, currently at line 483-506, current date: 2022-08-12)
2. (string)  the python struct format character fitting the onnx representation (found in https://docs.python.org/3/library/struct.html)
3. (string)  a readable string of the datatype

TODO erweiterbar kommentar
"""
datatype_mapping = [
    (1, "f", "float"),
    (2, "B", "int 8 (unsigned char)"),
    (3, "b", "int 8 (signed char)"),
    (4, "I", "unsigned int 16"),
    (5, "i", "int 16"),
    (6, "l", "int 32 (long)"),
    (7, "q", "int 64 (long long)"),
    (8, "s", "string (char[])"),
    (9, "?", "bool"),
    (10, "e", "IEEE754 half-precision floating-point format (16 bits wide)"),
    (11, "d", "double (float)"),
    (12, "L", "int 32 (unsigned long)"),
    (13, "Q", "int 64 (unsigned long long)"),
]

"""
following functions are for the convertion process
"""

def split_without_removal(string, delimiter):
    if delimiter in string:
        #need to call partition once more
        p = string.partition(delimiter)
        out = [p[0], p[1]]
        out.extend(split_without_removal(p[2], delimiter))
        return out
    else:
        #recursive tail
        return [string]

def count_brackets_without_rawdata(string):
    if(string.find("raw_data") != -1):
        #string contains raw_data field!
        return 0
    open_brackets = string.count("{")
    closed_brackets = string.count("}")
    return open_brackets - closed_brackets
    

def first_block_of_brackets_r(liste, brackets, before_first_bracket):
    if(len(liste) == 0 or (before_first_bracket == False and brackets <= 0)):
        return ""
    else:
        line = liste.pop(0)
        num = count_brackets_without_rawdata(line)
        if(before_first_bracket == True and num > 0):
            before_first_bracket = False
        brackets += num
        out = [line]
        out.extend(first_block_of_brackets_r(liste, brackets, before_first_bracket))
        return out

def first_block_of_brackets(liste):
    liste = "".join(liste)
    first = first_block_of_brackets_r(liste.splitlines(True), 0, True)
    return ("".join(first), liste[len("".join(first))::])

def count_dims_value(string):
    #method is applied to value ("dims: 4" or similar)
    if(string.count("dims") == 0):
        return 1 #no dims here
    else:
        return int(string.split(" ")[-1])

def count_dims(string):
    dims = string.splitlines()
    return math.prod(map(count_dims_value, dims))

def determine_datatype_value(string):
    #method is applied to value ("data_type: 1" or similar)
    if(string.count("data_type") == 0):
        return 0 #no data_type here
    else:
        return int(string.split(" ")[-1])

def determine_datatype(string):
    #search for first occurance of "data_type"
    lines = string.splitlines()
    return max(map(determine_datatype_value, lines))

def datatype_mapping_nice_string(datatype_mapping):
    first = datatype_mapping.pop()
    if(len(datatype_mapping) == 0):
        return first[2]
    else:
        return first[2] + ", " + datatype_mapping_nice_string(datatype_mapping)

def onnx_to_python_datatype(datatype, datatype_mapping_r, datatype_mapping):
    if(len(datatype_mapping_r) == 0):
        raise NotImplementedError("ONNX datatype '" + str(datatype) + "' currently not supported. Supported datatypes are: " + datatype_mapping_nice_string(datatype_mapping))
    first = datatype_mapping_r.pop(0)
    if(first[0] == datatype):
        return first[1]
    else:
        return onnx_to_python_datatype(datatype, datatype_mapping_r, datatype_mapping)

def get__raw_data_value(string):
    #method is applied to value ('raw_data: "PY=\276\303M\030\277"' or similar)
    if(string.count("raw_data") == 0):
        return 0 #no raw_data here
    else:
        return string.strip().replace("raw_data: ", "", 1)
        #buggy:
        #return string.split(" ")[-1]

def get__raw_data_r(strings):
    if(len(strings) == 0):
        return None
    first = strings.pop(0)
    value = get__raw_data_value(first)
    if(value == 0):
        return get__raw_data_r(strings)
    else:
        return value[1:-1]   #remove quotation mark at beginning and end

def get__raw_data(string):
    lines = string.splitlines()
    return get__raw_data_r(lines)

def convert__raw_data(string):
    dims = count_dims(string)
    datatype = onnx_to_python_datatype(determine_datatype(string), copy.deepcopy(datatype_mapping), copy.deepcopy(datatype_mapping))
    raw_data = get__raw_data(string)
    if(raw_data != None):
        e = 'struct.unpack_from(dims*datatype, b"' + raw_data + '", 0)'
        converted_tuple = eval(e)
        list_data_converted = functools.reduce(lambda x,y: x+y, list(map(lambda x: 'data_converted: ' + x + '\n', map(str, converted_tuple))))
        string = replace__raw_data(string, list_data_converted)
    return string

def replace__raw_data_r(lines, converted):
    if(len(lines) == 0):
        return ""
    first = lines.pop(0)
    index = first.find("raw_data")
    if(index != -1):
        s = first[:(index)] + converted
        return s  + "\n" + replace__raw_data_r(lines, converted)
    else:
        return first + "\n" + replace__raw_data_r(lines, converted)

def replace__raw_data(string, converted):
    lines = string.splitlines()
    return replace__raw_data_r(lines, converted)
    
def modify(string):
    both = first_block_of_brackets(list(string))
    focus = both[0]
    rest = both[1]
    return convert__raw_data(focus) + rest

def modify_after_initializer(input_list, after_initializer):
    if(len(input_list) == 0):
        #list is empty, recursive tail
        return []
    first = input_list.pop(0)
    if(after_initializer):
        out = [modify(first)]
    else:
        out = [first]
    if(first == "initializer"):
        out.extend(modify_after_initializer(input_list, True))
    else:
        out.extend(modify_after_initializer(input_list, False))
    return out

def convert(string):
    converted = "".join(modify_after_initializer(split_without_removal(string, "initializer"), False))
    if "raw_data" in converted:
        raise NotImplementedError("A raw_data field remains after convertion. This usually means that the input contains a raw_data field outside of an initializer.")
    return converted

"""
end of convertion process
"""

def main():
    #check for correct number of arguments
    if(len(sys.argv) != 3):
        print("Expected 2 arguments instead of", len(sys.argv)-1)
        print("Please use the following program call:", sys.argv[0] , "<input file> <output file>")
        return

    input_file = sys.argv[1]
    output_file = sys.argv[2]

    #check for same name of input file and output file (since I dont know what will happen this is forbidden)
    if(input_file == output_file):
        print("Input file and output file can not be the same")
        return

    #try to open the input file, raise error when not exist
    try:
        f = open(input_file, "r")
        onnx_input_file = f.read()
    except FileNotFoundError:
        print("The file", input_file, "does not exist.")
        return

    #checks if output file already exists, if so ask user if it should be overwritten
    try:
        out = open(output_file, "x")
    except FileExistsError:
        cont = input("<" + output_file + "> already exists. Do you wish to continue? (<" + output_file + "> will be overwritten.) [y/n]: ")
        while(True):
            if(cont == "n" or cont == "N" or cont == "no" or cont == "No"):
                print("Process has been terminated by user, no files written.")
                return
            elif(cont == "y" or cont == "Y" or cont == "yes" or cont == "Yes"):
                out = open(output_file, "w")
                break
            else:
                cont = input("please type <y> or <n>: ")
                
    #convert
    try:
        convertion = convert(onnx_input_file)
    except Exception as e:
        convertion = "Error: something went wrong in raw_data converter: " + str(e)

    #if output ends with ".v", a coq file will be created

    if(output_file.endswith(".v")):
        print("Output file ends with '.v', so a coq file will be created")

        #double the quotation mark, so coq doesnt interpret them as string endlings
        convertion = convertion.replace('"', '""')

        pre = """(*this file was generated automatically by """+sys.argv[0]+"""*)
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.

Definition onnx_file : list ascii := list_ascii_of_string "
"""

        after = """"."""

        convertion = pre + convertion + after
    
    #write file
    try:
        out.write(convertion)
    except Exception as e:
        print("something went wrong during file writing:")
        print(e)
        return
    
    print("converted successfully")
    
main()
