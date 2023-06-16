import struct
import copy
import math
import sys
import functools

#TODO formatting

#cuts string in a way that it starts with the char after the first opening bracket and end with the char after the last closing bracket. Examples:
#"hello[my name] is" -> "my name"
#"hello my name is" -> ""
#"hello [my name" -> ""
#"hello]my name[ is" -> ""
def cut_tillbracket(string):
    open_bracket_first_index = string.find("[")
    closed_bracket_last_index = len(string) - string[::-1].find("]") #string gets reverse, so last one is found
    if(string.find("]") == -1):
        closed_bracket_last_index = -1
    if(open_bracket_first_index == -1):
        return ""
    elif(closed_bracket_last_index == -1):
        return ""
    elif(open_bracket_first_index > closed_bracket_last_index):
        return ""
    else:
        return string[open_bracket_first_index+1:closed_bracket_last_index-1]

#recursive definition causing segmentation fault often

def makeCoqList_r(string, buffer, bracketcount, quotationmark):
    if(len(string) == 0):
        return [buffer.strip()]
    first = string.pop(0)
    if(first == ";" and bracketcount == 0 and not quotationmark):
        print("GOT"+buffer)
        return [buffer.strip()] + makeCoqList_r(string, "", bracketcount, quotationmark)
    if(first == "[" or first == "(" or first == "{"):
        return makeCoqList_r(string, buffer + first, bracketcount + 1, quotationmark)
    if(first == "]" or first == ")" or first == "}"):
        return makeCoqList_r(string, buffer + first, bracketcount - 1, quotationmark)
    if(first == '"' or first == "'"):
        return makeCoqList_r(string, buffer + first, bracketcount, not quotationmark)
    else:
        return makeCoqList_r(string, buffer + first, bracketcount, quotationmark)


#gets a string in coq-list format (without outer brackets), returns a list with the elements
def makeCoqList(string):
    #return makeCoqList_r(list(string), "", 0, False)
    out = []
    buffer = ""
    bracketcount = 0
    quotationmark = False
    for first in string:
        if(first == ";" and bracketcount == 0 and not quotationmark):
            out += [buffer.strip()]
            buffer = ""
        elif(first == "[" or first == "(" or first == "{"):
            buffer += first
            bracketcount += 1
        elif(first == "]" or first == ")" or first == "}"):
            buffer += first
            bracketcount -= 1
        elif(first == '"' or first == "'"):
            buffer += first
            quotationmark = not quotationmark
        else:
            buffer += first
    return out + [buffer]
  

#gets a string representing a coq constructor as well as the position of the name argument in the string, returns a valid name
def makeName(string, name_argument_pos):
    split = string.split()
    name = split[name_argument_pos]
    name = name.replace('"', "")
    name = name.replace("'", "")
    name = name.replace(".", "")
    name = name.replace(":", "")
    
    #replace numbers with their names
    name = name.replace("0", "_zero_")
    name = name.replace("1", "_one_")
    name = name.replace("2", "_two_")
    name = name.replace("3", "_three_")
    name = name.replace("4", "_four_")
    name = name.replace("5", "_five_")
    name = name.replace("6", "_six_")
    name = name.replace("7", "_seven_")
    name = name.replace("8", "_eight_")
    name = name.replace("9", "_nine_")
    l = name.split()
    return l[0]

def delete_empty_string(l):
    out = []
    for s in l:
        if(len(s) > 0):
            out += [s]
    return out

#gets a string representing a coq constructor with values and returns the name and values in a list
def getCoqFunctionArguments(string):
    out = []
    buffer = ""
    bracketcount = 0
    quotationmark = False
    for first in string:
        if(first == " " and bracketcount == 0 and not quotationmark):
            out += [buffer.strip()]
            buffer = ""
        elif(first == "[" or first == "(" or first == "{"):
            buffer += first
            bracketcount += 1
        elif(first == "]" or first == ")" or first == "}"):
            buffer += first
            bracketcount -= 1
        elif(first == '"' or first == "'"):
            buffer += first
            quotationmark = not quotationmark
        else:
            buffer += first
    out += [buffer]
    return delete_empty_string(out)



#gets a string representing a coq function to string, changes it to coq function to R with inserting the termn 'real_of_string'
def funString_tofunR(string):
    out = ""
    inmarks = False
    for s in string:
        if(s == '"' and not inmarks):
            out += "real_of_string "
            inmarks = not inmarks 
        elif(s == '"' and inmarks):
            inmarks = not inmarks 
        out += s
    return out

#formats NNSequential_IR__initializer_matrix__python type
def format_NNSequential_IR__initializer_matrix__python(string):
    args = getCoqFunctionArguments(string)
    dim1 = args[3]
    dim2 = args[2]
    fun = args[4]
    var_name = makeName(string, 1)
    return "Definition " + var_name  + " := mk_matrix " + dim1 + " " + dim2 + " " + funString_tofunR(fun) + ".\n\n"

#formats NNSequential_IR__initializer_vector__python type
def format_NNSequential_IR__initializer_vector__python(string):
    args = getCoqFunctionArguments(string)
    dim = args[2]
    fun = args[3]
    var_name = makeName(string, 1)
    return "Definition " + var_name + " := mk_colvec " + dim + " " + funString_tofunR(fun) + ".\n\n"

#formats NNSequential_IR__Output__python type
def format_NNSequential_IR__Output__python(string):
    args = getCoqFunctionArguments(string)
    dim = args[2]
    var_name = makeName(string, 1)
    return (var_name, "(NNOutput (output_dim:=" + dim + "))")

#formats NNSequential_IR__Linear__python type
def format_NNSequential_IR__Linear__python(string):
    args = getCoqFunctionArguments(string)
    var_name = makeName(string, 1)
    in_name = makeName(string, 2)
    in_weight = makeName(string, 3)
    in_bias = makeName(string, 4)
    transB = args[5]
    beta = args[6]
    if(float(beta[1:-1]) == 1.0):
        bias_prefix = ""
        bias_suffix = " "
    else:
        bias_prefix = "(constmult (real_of_string " + beta + ") "
        bias_suffix = ") "
    if(float(transB[1:-1]) == 0.0):
        weight_prefix = ""
        weight_suffix = " "
    else:
        weight_prefix = "(transpose "
        weight_suffix = ")"
    return "Definition " + var_name + " := NNLinear " + weight_prefix + in_weight + weight_suffix + " " + bias_prefix + in_bias + bias_suffix + in_name + ".\n\n"
    

#formats NNSequential_IR__ReLu__python type
def format_NNSequential_IR__ReLu__python(string):
    var_name = makeName(string, 1)
    in_name = makeName(string, 2)
    return "Definition " + var_name + " := NNReLU " + in_name + ".\n\n"

def formatString(string):
    fun_name = getCoqFunctionArguments(string)[0]
    if(fun_name == "NNSequential_initializer_matrix"):
        return format_NNSequential_IR__initializer_matrix__python(string)
    if(fun_name == "NNSequential_initializer_vector"):
        return format_NNSequential_IR__initializer_vector__python(string)
    if(fun_name == "NNSequential_Output"):
        return format_NNSequential_IR__Output__python(string)
    if(fun_name == "NNSequential_Linear"):
        return format_NNSequential_IR__Linear__python(string)
    if(fun_name == "NNSequential_ReLu"):
        return format_NNSequential_IR__ReLu__python(string)

def formatList(l):
    output_node_name = ("","")
    out = ""
    for s in l:
        if(getCoqFunctionArguments(s)[0] == "NNSequential_Output"):
            output_node_name = formatString(s)
        else:
            out += formatString(s)
    return out.replace(output_node_name[0], output_node_name[1])

def convert(raw_input):
    success = raw_input.split()[1]
    if(success == "Error"):
        return raw_input
    else:
        return formatList(makeCoqList(cut_tillbracket(raw_input)))

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
        raw_input = f.read()
    except FileNotFoundError:
        print("The file", input_file, "does not exist.")
        return

    #if output doesnt end with ".v", it must be appended
    if(not output_file.endswith(".v")):
        print("Output file must end with '.v'. You did not follow that rule, so '.v' will be appended. Don't worry :)")
        output_file += ".v"

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
        convertion = convert(raw_input)
    except Exception as e:
        print("something went wrong during convertion:")
        print(e)
        return

    

    pre = """(*this file was generated automatically by """+sys.argv[0]+"""*)
    From Coq Require Import Strings.String.
    From Coq Require Import Strings.Ascii.

    From Coq Require Import Reals.
    From Coquelicot Require Import Coquelicot.
    From CoqE2EAI Require Import piecewise_affine neuron_functions.
    From CoqE2EAI Require Import matrix_extensions.
    From CoqE2EAI Require Import neural_networks.
    From CoqE2EAI Require Import string_to_number.
    From CoqE2EAI Require Import transpose_mult_matrix.


    Open Scope nat_scope.
    """

    convertion = pre + convertion
    
    #write file
    try:
        out.write(convertion)
    except Exception as e:
        print("something went wrong during file writing:")
        print(e)
        return
    
    print("converted successfully")

main()
