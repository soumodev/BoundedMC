'''
GRAMMAR
formula : PROP
        | LITERAL
        | NOT formula
        | LPAR formula OR formula RPAR
        | LPAR formula AND formula RPAR
        | LPAR formula XOR formula RPAR
        | LPAR formula IFF formula RPAR
        | X formula
        | F formula
        | G formula
        | LPAR formula U formula RPAR
        | LPAR formula R formula RPAR
'''

import ply.yacc as yacc 
from parser.ply_lexer import tokens
from parser.formulas import *
import sys


def p_formula_prop(p):
  ''' formula : PROP '''
  p[0] = FormulaMonadic('PROP', p[1])

def p_formula_literal(p):
  ''' formula : LITERAL '''
  p[0] = FormulaMonadic('LITERAL', p[1])

def p_formula_not(p):
  ''' formula : NOT formula  '''
  p[0] = FormulaMonadic('NOT', p[2])

def p_formula_or(p):
  ''' formula : LPAR formula OR formula RPAR '''
  p[0] = FormulaDyadic('OR', p[2], p[4])

def p_formula_and(p):
  ''' formula : LPAR formula AND formula RPAR '''
  p[0] = FormulaDyadic('AND', p[2], p[4])

def p_formula_xor(p):
  ''' formula : LPAR formula XOR formula RPAR '''
  p[0] = FormulaMonadic('NOT', FormulaDyadic('AND', FormulaDyadic('OR', FormulaMonadic('NOT', p[2]), p[4]), FormulaDyadic('OR', FormulaMonadic('NOT', p[4]), p[2])))

def p_formula_iff(p):
  ''' formula : LPAR formula IFF formula RPAR '''
  p[0] =  FormulaDyadic('AND', FormulaDyadic('OR', FormulaMonadic('NOT', p[2]), p[4]), FormulaDyadic('OR', FormulaMonadic('NOT', p[4]), p[2]))

def p_formula_X(p):
  ''' formula : X formula '''
  p[0] = FormulaMonadic('X', p[2])

def p_formula_F(p):
  ''' formula : F formula '''
  p[0] = FormulaMonadic('F', p[2])

def p_formula_G(p):
  ''' formula : G formula '''
  p[0] = FormulaMonadic('G', p[2])

def p_formula_U(p):
  ''' formula : LPAR formula U formula RPAR '''
  p[0] = FormulaDyadic('U', p[2], p[4])

def p_formula_R(p):
  ''' formula : LPAR formula R formula RPAR '''
  p[0] = FormulaDyadic('R', p[2],  p[4])

def p_formula_par(p):
  ''' formula : LPAR formula RPAR '''
  p[0] = p[2]

def p_error(p):
  sys.exit("Syntax Error! Check your formula.")

parser = yacc.yacc()

