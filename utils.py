"""
Several utility functions
"""

from z3 import *
from parser.formulas import *

def trace_print(n_bits, length, model, loop = -1):
    """
    Prints out the trace as a neat sequence of states given a z3 sat model. Note that in the model,
    the variable for the ith bit of the kth state in the trace must be named s_k_i
    """
    
    print(''.join(['v%-3d'%i for i in range(n_bits)]))
    for k in range(length):
        print(''.join(['%-4d'%(1 if model.eval(Bool('s_%d_%d'%(k,i))) == True else 0) 
                                    for i in range(n_bits)]))
        if k == loop:
            print('Loop:')


def ast_to_nnf(ast):
    """
    Converts the AST of the LTL formula to NNF form. Note: this causes exponential blowup for U and
    R
    """
    if type(ast) == str:
        return ast
    if ast.type != 'NOT':
        if isinstance(ast, FormulaMonadic):
            return FormulaMonadic(ast.type, ast_to_nnf(ast.child))
        else:
            return FormulaDyadic(ast.type, ast_to_nnf(ast.left), ast_to_nnf(ast.right))
    if ast.child.type == 'NOT':
        return ast_to_nnf(ast.child.child)
    elif ast.child.type == 'LITERAL':
        return FormulaMonadic('LITERAL', 'fls' if ast.child.child == 'tru' else 'tru')
    elif ast.child.type == 'PROP':
        return FormulaMonadic('NEGPROP', ast.child.child)
    elif ast.child.type == 'AND':
        return FormulaDyadic('OR', ast_to_nnf(FormulaMonadic('NOT', ast.child.left)),
                                    ast_to_nnf(FormulaMonadic('NOT', ast.child.right)))
    elif ast.child.type == 'OR':
        return FormulaDyadic('AND', ast_to_nnf(FormulaMonadic('NOT', ast.child.left)),
                                    ast_to_nnf(FormulaMonadic('NOT', ast.child.right)))
    elif ast.child.type == 'X':
        return FormulaMonadic('X', ast_to_nnf(FormulaMonadic('NOT', ast.child.child)))
    elif ast.child.type == 'F':
        return FormulaMonadic('G', ast_to_nnf(FormulaMonadic('NOT', ast.child.child)))
    elif ast.child.type == 'G':
        return FormulaMonadic('F', ast_to_nnf(FormulaMonadic('NOT', ast.child.child)))
    elif ast.child.type == 'U':
        return FormulaDyadic('R', ast_to_nnf(FormulaMonadic('NOT', ast.child.left)),
                                    ast_to_nnf(FormulaMonadic('NOT', ast.child.right)))
    elif ast.child.type == 'R':
        return FormulaDyadic('U', ast_to_nnf(FormulaMonadic('NOT', ast.child.left)),
                                    ast_to_nnf(FormulaMonadic('NOT', ast.child.right)))


## DEBUG
#from parser.ply_parser import parser
#
#ast = parser.parse('!(F G !(a . (!b)))')
#print(ast_to_nnf(ast))
