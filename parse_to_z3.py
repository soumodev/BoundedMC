"""
Defines functions to convert string representations of predicates and transitions to functions from
lists of (pairs of lists of) z3 variables to z3 expressions. 
"""

from parser.ply_parser import parser

from parser.formulas import *
import z3

def parse_pred_z3_gen(pred, n_bits):
    """
    Parses the given string or ast representation of a predicate over `n_bits` to a function generating a
    z3 expression from a set of given z3 variables. The predicate must be a not use any LTL
    operators, and the propositional variables used must be of the form `vi`, referring to the
    predicate where `i`-th bit is true. All other connectives allowed in the LTL expression grammar
    may be used. Note that `i` must not exceed `n_bits`. Also, the returned function expects a list
    of length exactly `n_bits`, any other length will result in index errors.
    """

    if type(pred) == str:
        ast = parser.parse(pred)
    elif isinstance(pred, Formula):
        ast = pred
    else:
        raise "Can only parse strings and ast to z3 expression generators"
    
    # Recursively generate the [z3_var] -> z3_expr function from an ast
    def rec_get_z3_gen(node):
        if isinstance(node, FormulaMonadic):
            if node.type == 'PROP':
                if node.child[0] != 'v' or int(node.child[1:]) >= n_bits:
                    raise 'ERROR: Variable in predicate must be of form vi, i < n_bits'
                return lambda z3_vars: z3_vars[int(node.child[1:])]
            elif node.type == 'LITERAL':
                return lambda z3_vars: z3.BoolVal(True if node.child == 'tru' else False)
            elif node.type == 'NOT':
                return lambda z3_vars: z3.Not(rec_get_z3_gen(node.child)(z3_vars))
            else:
                raise 'ERROR: Predicate uses disallowed unary token'
        elif isinstance(node, FormulaDyadic):
            if node.type == 'OR':
                return lambda z3_vars: z3.Or(rec_get_z3_gen(node.left)(z3_vars), 
                                                rec_get_z3_gen(node.right)(z3_vars))
            elif node.type == 'AND':
                return lambda z3_vars: z3.And(rec_get_z3_gen(node.left)(z3_vars), 
                                                rec_get_z3_gen(node.right)(z3_vars))
            else:
                raise 'ERROR: Predicate uses disallowed binary connective'
        else:
            raise "ERROR: Ast node is not monadic or dyadic"

    return rec_get_z3_gen(ast)

def parse_trans_z3_gen(pred, n_bits):
    """
    Parses the given string or ast representation of a transition relation over `n_bits` to a function generating a
    z3 expression from a set of given z3 variables. The transition relation must be a not use any LTL
    operators, and the propositional variables used must be of the form `ui`, referring to the
    transition relation which holds whenever the `i`-th bit of the left state is true, and `vi`,
    referring to the transition relation which holds whenever the `i`-th bit of the right variable
    is true. All other connectives allowed in the LTL expression grammar may be used. Note that `i`
    must not exceed `n_bits`. Also, the returned function expects lists of length exactly `n_bits`,
    any other length will result in index errors.
    """

    if type(pred) == str:
        ast = parser.parse(pred)
    elif isinstance(pred, Formula):
        ast = pred
    else:
        raise "Can only parse strings and ast to z3 expression generators"
    
    
    # Recursively generate the [z3_var] -> z3_expr function from an ast
    def rec_get_z3_gen(node):
        if isinstance(node, FormulaMonadic):
            if node.type == 'PROP':
                if int(node.child[1:]) >= n_bits:
                    raise 'ERROR: Index of variable must not be more than n_bits'
                if node.child[0] == 'u':
                    return lambda z3_l, z3_r: z3_l[int(node.child[1:])]
                elif node.child[0] == 'v':
                    return lambda z3_l, z3_r: z3_r[int(node.child[1:])]
                else:
                    raise 'ERROR: Variable must be `ui` or `vi`'
            elif node.type == 'LITERAL':
                return lambda z3_l, z3_r: z3.BoolVal(True if node.child == 'tru' else False)
            elif node.type == 'NOT':
                return lambda z3_l, z3_r: z3.Not(rec_get_z3_gen(node.child)(z3_l, z3_r))
            else:
                raise 'ERROR: Transition uses disallowed unary token'
        elif isinstance(node, FormulaDyadic):
            if node.type == 'OR':
                return lambda z3_l, z3_r: z3.Or(rec_get_z3_gen(node.left)(z3_l, z3_r), 
                                                rec_get_z3_gen(node.right)(z3_l, z3_r))
            elif node.type == 'AND':
                return lambda z3_l, z3_r: z3.And(rec_get_z3_gen(node.left)(z3_l, z3_r), 
                                                rec_get_z3_gen(node.right)(z3_l, z3_r))
            else:
                raise 'ERROR: Transition uses disallowed binary connective'
        else:
            raise 'ERROR: Ast node is not monadic or dyadic'

    return rec_get_z3_gen(ast)

#DEBUG

#pred = '(v0 + (v1.v2))'
#trans = '(u0 + (u1.v1))'
#
#pred_gen = parse_pred_z3_gen(pred, 3)
#trans_gen = parse_trans_z3_gen(trans, 3)
#
#print(pred_gen([z3.Bool('u'), z3.Bool('v'), z3.Bool('w')]))
#print(trans_gen([z3.Bool('u'), z3.Bool('v'), z3.Bool('w')], 
#                [z3.Bool('u_'), z3.Bool('v_'), z3.Bool('w_')]))
#
#ctl = '((X (F v0)) U (F v0))'
#print(parser.parse(ctl).vp)
#print(parser.parse(ctl).left.child.vp)
#print(parser.parse(ctl).right.vp)
