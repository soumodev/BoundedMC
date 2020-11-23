"""
Several utility functions
"""

from z3 import *

def trace_print(n_bits, length, model):
    """
    Prints out the trace as a neat sequence of states given a z3 sat model. Note that in the model,
    the variable for the ith bit of the kth state in the trace must be named s_k_i
    """
    
    print(''.join(['v%-3d'%i for i in range(n_bits)]))
    for k in range(length):
        print(''.join(['%-4d'%(1 if model.eval(Bool('s_%d_%d'%(k,i))) == True else 0) 
                                    for i in range(n_bits)]))
