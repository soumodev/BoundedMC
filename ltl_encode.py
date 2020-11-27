"""
Define functions to encode the expression for a k-long counterexample to an arbitrary LTL formula in
SMT.

To make sure that the resulting formula is polynomial in the length of the path, we introduce
one variable for each subexpression, i, k and l. If `ast` is the syntax tree for some
expression, then `ast.vp` gives a string that is unique for that expression, and the non looping
variable for i,k is encoded as `nl_ast.vp_k_i`, and the looping variable is encoded as
`lp_ast.vp_k_i_l`. Then, the constraints added represent the relations between the various
variables according to the translation rules given. There are upto k many variables of this kind
for each subexpression. For each variable, we have exactly one constraint 'defining' that
variable in terms of the others. For all operators, the size of this 'definition' is atmost
linear in k. Thus, the total length of the encoding is atmost quadratic in k.

We define prefixes that are unique for each unique subexpression in the formula (see
`parser/formula.py`) so that we do not end up with seperate variables for the same
subexpression. For each variable `var`, we have a constraint that 'defines' var, and is of the
form `var == ....`. The functions defined here add this 'definition' for the top level
expressoin to the solver passed, and recursively call the encoder functions to add the
defintions for all the variables appearing in the rhs of the above constraint.

If any of these functions are called twice with asts representing the same variable and for the
same i, k, and l at some point during the recursion, we will end up with two copies of the exact
same constraint. We prevent this by passing a set of all the variables already added, call it
`def_vars`, and do not add constraints for these again.

Note that in the bmc loop, the `def_vars` is not cleared between iterations, and the constraints
added to the solver for the translation are not removed. This will mean that the clauses derived
by z3 for the constraints in the previous iterations can be reused. It will also lead to some
extra equalities being present in the solver. Note that these will just be 'definitions' of
variables that are not relevant to the current bmc iteration, but are nonetheless valid, and
will not rule out any traces. For instance, if we are checking `Xf` for some `k`, `[Xf]0,k = [f]1,k`
will be a relevant 'definition' which the solver will have, but the solver will also have the
'definition' `[Xf]0,(k-1) = [f]1,(k-1)` will also be a 'definition' that the solver will have.
This does not appear in the recursive expansion of `[Xf]0,k`, and is not relevant to the current
query of `[Xf]0,k`, but is nonetheless valid and will not affect the sat checks.

Note that at any point, the set of clauses added by the encoding functions recursively define a
bunch of variables in terms of the variables representing which state bits are true at any given
time, encoded as `s_t_i` for the `i`-th bit at time `t`. So, nomatter what the value of these
variables are, we can assign values to the rest of the subexpression variables in a manner that
satisfies all the definitions by simply reading off the definitions in the reverse order of
addition. Thus, the set of constraints added is always sat. Also note that the non-looping case
and the looping case define completely seperate sets of variables, and thus the constraints
added to the solver by this functions are independent. So, if the constraints for the non
looping case is present during the query of the looping case, since the set of variables are
different, the sat query is not affected. This fact is used by the bmc loops using this
function.

"""

from z3 import *
from parser.formulas import *

def nonLooping(ast,i,k,solver,mem):
    """
    Given the `ast` of a formula, adds to the z3 `solver` constraints representing the partial
    nonlooping translation of the formula starting at the position `i`, for a path of length `k`, 
    according to the recursive relation given in class. 
    """
    if 'nl_%s_%d_%d'%(ast.vp,k,i) in mem:
        return
    else:
        mem.add('nl_%s_%d_%d'%(ast.vp,k,i))
    
    if ast.type == "PROP":
        z = Bool("nl_%s_%d_%d"%(ast.vp,k,i))
        p=Bool("s_%d_%d"%(k, int(ast.child[1:])))
        solver.add(z==p)

    elif ast.type == "NEGPROP":
        z = Bool("nl_%s_%d_%d"%(ast.vp,k,i))
        p=Bool("s_%d_%d"%(k, int(ast.child[1:])))
        solver.add(z==Not(p))

    elif ast.type == "LITERAL":
        z = Bool("nl_%s_%d_%d"%(ast.vp,k,i))
        solver.add(z==ast.child)

    elif ast.type =="OR":
        z = Bool("nl_%s_%d_%d"%(ast.vp,k,i))
        x = Bool("nl_%s_%d_%d"%(ast.left.vp,k,i))
        y = Bool("nl_%s_%d_%d"%(ast.right.vp,k,i))
        solver.add(z==Or(x,y))
        nonLooping(ast.left,i,k,solver,mem)
        nonLooping(ast.right,i,k,solver,mem)

    elif ast.type =="AND":
        z = Bool("nl_%s_%d_%d"%(ast.vp,k,i))
        x = Bool("nl_%s_%d_%d"%(ast.left.vp,k,i))
        y = Bool("nl_%s_%d_%d"%(ast.right.vp,k,i))
        solver.add(z==And(x,y))
        nonLooping(ast.left,i,k,solver,mem)
        nonLooping(ast.right,i,k,solver,mem)

    elif ast.type == "X":
        z = Bool("nl_%s_%d_%d"%(ast.vp,k,i))
        if(i < k):
          x = Bool("nl_%s_%d_%d"%(ast.child.vp,k,i+1))
          solver.add(z==x)
        else:
            solver.add(z==False)
        nonLooping(ast.child,i,k,solver,mem)

    elif ast.type == "G":
        z = Bool("nl_%s_%d_%d"%(ast.vp,k,i))
        solver.add(z==False)

    elif ast.type == "F":
        z = Bool("nl_%s_%d_%d"%(ast.vp,k,i))
        x = Bool("nl_%s_%d_%d"%(ast.child.vp,k,i))
        z_next = Bool("nl_%s_%d_%d"%(ast.vp,k,i+1))
        if i == k:
          solver.add(z==x)
        elif i < k:
          solver.add(z==Or(x,z_next))
          nonLooping(ast,i+1,k,solver,mem)
        nonLooping(ast.child,i,k,solver,mem)
    
    elif ast.type == "U":
        z = Bool("nl_%s_%d_%d"%(ast.vp,k,i))
        g_ik = Bool("nl_%s_%d_%d"%(ast.right.vp,k,i))
        f_ik = Bool("nl_%s_%d_%d"%(ast.left.vp,k,i))
        z_next = Bool("nl_%s_%d_%d"%(ast.vp,k,i+1))
        if i == k:
          solver.add(z==g_ik)
        else:
          solver.add(z==Or(g_ik,And(f_ik,z_next)))
          nonLooping(ast,i+1,k,solver,mem)
        nonLooping(ast.left,i,k,solve,mem)
        nonLooping(ast.right,i,k,solver,mem)
        
    elif ast.type == "R":
        z = Bool("nl_%s_%d_%d"%(ast.vp,k,i))
        g_ik = Bool("nl_%s_%d_%d"%(ast.right.vp,k,i))
        f_ik = Bool("nl_%s_%d_%d"%(ast.left.vp,k,i))
        z_next = Bool("nl_%s_%d_%d"%(ast.vp,k,i+1))
        if i == k:
          solver.add(z==Or(g_ik,f_ik))
        else:
          solver.add(z==Or(f_ik,And(g_ik,z_next)))
          nonLooping(ast,i+1,k,solver,mem)
        nonLooping(ast.right,i,k,solver,mem)
        nonLooping(ast.left,i,k,solve,mem)


def ltl_looping_encode(start_pos, loop_pos, end_pos, ast, solver, def_vars):
    """
    Given the `ast` of a formula, adds to the z3 `solver` constraints representing the partial
    looping translation of the formula starting at the position `start_pos` (i in the lecture
    notation), for a path of length `end_pos` (k) looping at the position `loop_pos` (l), according
    to the recursive relation given in class. 
    """
    #def ltl_looping(start_pos, loop_pos, end_pos, ast, solver, def_vars):

    # Sanity
    assert isinstance(ast, Formula) and start_pos <= end_pos and loop_pos <= end_pos
    
    this_var = 'lp_%s_%d_%d_%d'%(ast.vp, end_pos, start_pos, loop_pos)
    # Check def_vars, if variable is present, terminate.
    if this_var in def_vars:
        return
    
    # Add vp to def_vars
    def_vars.add(this_var)

    # Add constraints based on translation rules, and make recursive calls to include all relevant
    # definitions
    if ast.type == 'PROP':
        solver.add( Bool(this_var) ==
                Bool('s_%d_%d'%(start_pos, int(ast.child[1:]))))
    
    
    elif ast.type == 'NEGPROP':
        solver.add( Bool(this_var) ==
                Not( Bool('s_%d_%d'%(start_pos, int(ast.child[1:])))))
    
    
    elif ast.type == 'AND':
        solver.add( Bool(this_var) ==
                And( Bool('lp_%s_%d_%d_%d'%(ast.left.vp, end_pos, start_pos, loop_pos)),
                     Bool('lp_%s_%d_%d_%d'%(ast.right.vp, end_pos, start_pos, loop_pos))))
        ltl_looping_encode(start_pos, loop_pos, end_pos, ast.left, solver, def_vars)
        ltl_looping_encode(start_pos, loop_pos, end_pos, ast.right, solver, def_vars)
    
    
    elif ast.type == 'OR':
        solver.add( Bool(this_var) ==
                Or( Bool('lp_%s_%d_%d_%d'%(ast.left.vp, end_pos, start_pos, loop_pos)),
                     Bool('lp_%s_%d_%d_%d'%(ast.right.vp, end_pos, start_pos, loop_pos))))
        ltl_looping_encode(start_pos, loop_pos, end_pos, ast.left, solver, def_vars)
        ltl_looping_encode(start_pos, loop_pos, end_pos, ast.right, solver, def_vars)
    
    
    elif ast.type == 'X':
        nxt_pos = start_pos+1 if start_pos<end_pos else loop_pos
        solver.add( Bool(this_var) ==
                Bool('lp_%s_%d_%d_%d'%(ast.child.vp, end_pos, nxt_pos, loop_pos)))
        ltl_looping_encode(nxt_pos, loop_pos, end_pos, ast.child, solver, def_vars)
    
    
    elif ast.type == 'G':
        
        if start_pos < loop_pos:
            # l[Gf]i,k i<l = l[f]i,k /\ l[Gf](i+1),k
            solver.add( Bool(this_var) ==
                And( Bool('lp_%s_%d_%d_%d'%(ast.child.vp, end_pos, start_pos, loop_pos)),
                     Bool('lp_%s_%d_%d_%d'%(ast.vp, end_pos, start_pos+1, loop_pos))))
            ltl_looping_encode(start_pos, loop_pos, end_pos, ast.child, solver, def_vars)
            ltl_looping_encode(start_pos+1, loop_pos, end_pos, ast, solver, def_vars)
        
        elif start_pos == loop_pos:
            # In this case we loop-expand
            solver.add( Bool(this_var) ==
                And([ Bool('lp_%s_%d_%d_%d'%(ast.child.vp, end_pos, i, loop_pos))
                                                    for i in range(loop_pos, end_pos+1) ]))
            for i in range(loop_pos, end_pos+1):
                ltl_looping_encode(i, loop_pos, end_pos, ast.child, solver, def_vars)
        
        else:
            # l[Gf]i,k i>l = l[Gf]l,k
            solver.add( Bool(this_var) ==
                    Bool('lp_%s_%d_%d_%d'%(ast.vp, end_pos, loop_pos, loop_pos)))
            ltl_looping_encode(loop_pos, loop_pos, end_pos, ast, solver, def_vars)

    elif ast.type == 'F':
        
        if start_pos < loop_pos:
            # l[Ff]i,k i<l = l[f]i,k \/ l[Ff](i+1),k
            solver.add( Bool(this_var) ==
                Or( Bool('lp_%s_%d_%d_%d'%(ast.child.vp, end_pos, start_pos, loop_pos)),
                     Bool('lp_%s_%d_%d_%d'%(ast.vp, end_pos, start_pos+1, loop_pos))))
            ltl_looping_encode(start_pos, loop_pos, end_pos, ast.child, solver, def_vars)
            ltl_looping_encode(start_pos+1, loop_pos, end_pos, ast, solver, def_vars)
        
        elif start_pos == loop_pos:
            # In this case we loop-expand
            solver.add( Bool(this_var) ==
                Or([ Bool('lp_%s_%d_%d_%d'%(ast.child.vp, end_pos, i, loop_pos))
                                                    for i in range(loop_pos, end_pos+1) ]))
            for i in range(loop_pos, end_pos+1):
                ltl_looping_encode(i, loop_pos, end_pos, ast.child, solver, def_vars)
        
        else:
            # l[Ff]i,k i>l = l[Ff]l,k
            solver.add( Bool(this_var) ==
                    Bool('lp_%s_%d_%d_%d'%(ast.vp, end_pos, loop_pos, loop_pos)))
            ltl_looping_encode(loop_pos, loop_pos, end_pos, ast, solver, def_vars)


    elif ast.type == 'U':
        # Now, to encode U, we add two new sets of variables:
        # auxuik_ast.vp_k_i_l = \/j=i->k(l[g]j,k /\n=i->(j-1) l[f]n,k)
        # auxuli_ast.vp_k_i_l = \/j=l->(i-1)(l[g]j,k /\n=l->(j-1) l[f]n,k)
        # then, we will have 
        # l[fUg]i,k = auxuik_ast.vp_k_i_l \/ (auxuli_ast.vp_k_i_l /\n=i->k l[f]n,k) if i > l
        # l[fUg]i,k = auxuik_ast.vp_k_i_l                                           otherwise
        #
        # We define helper functions to encode these variables
        def auxuik_encode(i, l, k, ast, solver, def_vars):
            this_vname = 'auxuik_%s_%d_%d_%d'%(ast.vp, k, i, l)
            if this_vname in def_vars:
                return
            def_vars.add(this_vname)
            
            if i == k:
                # Base case
                solver.add( Bool(this_vname) ==  
                        Bool('lp_%s_%d_%d_%d'%(ast.right.vp, k, k, l)))
                ltl_looping_encode(k, l, k, ast.right, solver, def_vars)
            else:
                # Recursive case
                solver.add( Bool(this_vname) ==
                        Or( Bool('lp_%s_%d_%d_%d'%(ast.right.vp, k, i, l)),
                           And( Bool('lp_%s_%d_%d_%d'%(ast.left.vp, k, i, l)),
                                Bool('auxuik_%s_%d_%d_%d'%(ast.vp, k, i+1, l)))))
                ltl_looping_encode(i, l, k, ast.right, solver, def_vars)
                ltl_looping_encode(i, l, k, ast.left, solver, def_vars)
                auxuik_encode(i+1, l, k, ast, solver, def_vars)
        
        def auxuli_encode(i, l, k, ast, solver, def_vars):
            assert i>l      # Sanity check

            this_vname = 'auxuli_%s_%d_%d_%d'%(ast.vp, k, i, l)
            if this_vname in def_vars:
                return
            def_vars.add(this_vname)
            
            if i == l+1:
                # Base case
                solver.add( Bool(this_vname) == 
                        Bool('lp_%s_%d_%d_%d'%(ast.right.vp, k, l, l)))
                ltl_looping_encode(l, l, k, ast.right, solver, def_vars)
            else:
                # Recursive case
                solver.add( Bool(this_vname) ==
                        Or( Bool('auxuli_%s_%d_%d_%d'%(ast.vp, k, i-1, l)),
                            And( Bool('lp_%s_%d_%d_%d'%(ast.right.vp, k, i-1, l)),
                            And([ Bool('lp_%s_%d_%d_%d'%(ast.left.vp, k, n, l))
                                        for n in range(l, i-1) ]))))
                auxuik_encode(i-1, l, k, ast, solver, def_vars)
                ltl_looping_encode(i-1, l, k, ast.right, solver, def_vars)
                for n in range(l, i-1):
                    ltl_looping_encode(n, l, k, ast.left, solver, def_vars)
        
        # Now, we finally define l[fUg]i,k
        if start_pos <= loop_pos:
            solver.add( Bool(this_var) ==
                    Bool('auxuik_%s_%d_%d_%d'%(ast.vp, end_pos, start_pos, loop_pos)))
            auxuik_encode(start_pos, loop_pos, end_pos, ast, solver, def_vars)
        else:
            solver.add( Bool(this_var) ==
                    Or( Bool('auxuik_%s_%d_%d_%d'%(ast.vp, end_pos, start_pos, loop_pos)), 
                        And( Bool('auxuli_%s_%d_%d_%d'%(ast.vp, end_pos, start_pos, loop_pos)),
                        And([ Bool('lp_%s_%d_%d_%d'%(ast.left.vp, end_pos, n, loop_pos))
                                            for n in range(start_pos, end_pos+1) ]))))
            auxuik_encode(start_pos, loop_pos, end_pos, ast, solver, def_vars)
            auxuli_encode(start_pos, loop_pos, end_pos, ast, solver, def_vars)
            for n in range(start_pos, end_pos+1):
                ltl_looping_encode(n, loop_pos, end_pos, ast.left, solver, def_vars)
                           

    elif ast.type == 'R':
        # Now, to encode R, we add two new sets of variables:
        # auxRik_ast.vp_k_i_l = \/j=i->k (l[f]j,k /\n=i->j l[g]n,k)
        # auxRli_ast.vp_k_i_l = \/j=l->(i-1) (l[f]j,k /\n=l->j l[g]n,k)
        # then, we will have 
        # l[fUg]i,k = auxuik_ast.vp_k_i_l \/ (auxuli_ast.vp_k_i_l /\n=i->k l[g]n,k) \/ l[Gg]i,k if i > l
        # l[fUg]i,k = auxuik_ast.vp_k_i_l \/ l[Gg]i,k                                          otherwise
        #
        # We define helper functions to encode these variables
        def auxrik_encode(i, l, k, ast, solver, def_vars):
            this_vname = 'auxrik_%s_%d_%d_%d'%(ast.vp, k, i, l)
            if this_vname in def_vars:
                return
            def_vars.add(this_vname)
            
            if i == k:
                # Base case
                solver.add( Bool(this_vname) ==
                        And( Bool('lp_%s_%d_%d_%d'%(ast.left.vp, k, k, l)),
                            Bool('lp_%s_%d_%d_%d'%(ast.right.vp, k, k, l))))
                ltl_looping_encode(k, l, k, ast.left, solver, def_vars)
                ltl_looping_encode(k, l, k, ast.right, solver, def_vars)
            else:
                # Recursive case
                solver.add( Bool(this_vname) ==
                        Or(And( Bool('lp_%s_%d_%d_%d'%(ast.left.vp, k, i, l)),
                                Bool('lp_%s_%d_%d_%d'%(ast.right.vp, k, i, l))),
                           And( Bool('lp_%s_%d_%d_%d'%(ast.right.vp, k, i, l)),
                                Bool('auxrik_%s_%d_%d_%d'%(ast.vp, k, i+1, l)))))
                ltl_looping_encode(i, l, k, ast.right, solver, def_vars)
                ltl_looping_encode(i, l, k, ast.left, solver, def_vars)
                auxrik_encode(i+1, l, k, ast, solver, def_vars)
        
        def auxrli_encode(i, l, k, ast, solver, def_vars):
            assert i>l      # Sanity check

            this_vname = 'auxrli_%s_%d_%d_%d'%(ast.vp, k, i, l)
            if this_vname in def_vars:
                return
            def_vars.add(this_vname)
            
            if i == l+1:
                # Base case
                solver.add( Bool(this_vname) ==
                        And( Bool('lp_%s_%d_%d_%d'%(ast.left.vp, k, l, l)), 
                            Bool('lp_%s_%d_%d_%d'%(ast.right.vp, k, l, l))))
                ltl_looping_encode(l, l, k, ast.left, solver, def_vars)
                ltl_looping_encode(l, l, k, ast.right, solver, def_vars)
            else:
                # Recursive case
                solver.add( Bool(this_vname) ==
                        Or( Bool('auxrli_%s_%d_%d_%d'%(ast.vp, k, i-1, l)),
                            And( Bool('lp_%s_%d_%d_%d'%(ast.left.vp, k, i-1, l)),
                            And([ Bool('lp_%s_%d_%d_%d'%(ast.right.vp, k, n, l))
                                        for n in range(l, i) ]))))
                auxrik_encode(i-1, l, k, ast, solver, def_vars)
                ltl_looping_encode(i-1, l, k, ast.left, solver, def_vars)
                for n in range(l, i):
                    ltl_looping_encode(n, l, k, ast.right, solver, def_vars)
        
        # Now, we finally define l[fUg]i,k
        gg_ast = FormulaMonadic('G', ast.right)
        gg_var = Bool('lp_%s_%d_%d_%d'%(gg_ast.vp, end_pos, start_pos, loop_pos))
        if start_pos <= loop_pos:
            # l[fUg]i,k = auxuik_ast.vp_k_i_l \/ l[Gg]i,k                                          
            solver.add( Bool(this_var) ==
                    Or( Bool('auxrik_%s_%d_%d_%d'%(ast.vp, end_pos, start_pos, loop_pos)),
                        gg_var))
            auxrik_encode(start_pos, loop_pos, end_pos, ast, solver, def_vars)
            ltl_looping_encode(start_pos, loop_pos, end_pos, gg_ast, solver, def_vars)
        else:
            # l[fUg]i,k = auxuik_ast.vp_k_i_l \/ (auxuli_ast.vp_k_i_l /\n=i->k l[g]n,k) \/ l[Gg]i,k
            solver.add( Bool(this_var) == 
                    Or( Bool('auxuik_%s_%d_%d_%d'%(ast.vp, end_pos, start_pos, loop_pos)), gg_var, 
                        And( Bool('auxuli_%s_%d_%d_%d'%(ast.vp, end_pos, start_pos, loop_pos)),
                        And([ Bool('lp_%s_%d_%d_%d'%(ast.left.vp, end_pos, n, loop_pos))
                                            for n in range(start_pos, end_pos+1) ]))))
            auxuik_encode(start_pos, loop_pos, end_pos, ast, solver, def_vars)
            auxuli_encode(start_pos, loop_pos, end_pos, ast, solver, def_vars)
            ltl_looping_encode(start_pos, loop_pos, end_pos, gg_ast, solver, def_vars)
            for n in range(start_pos, end_pos+1):
                ltl_looping_encode(n, loop_pos, end_pos, ast.left, solver, def_vars)
     


# DEBUG

from parser.ply_parser import *
from utils import *
from parse_to_z3 import *

init = "((!v0) . (!v1))"
trans = "(((!u0) . ((!u1) . ((!v0) .   v1))) + \
         (((!u0) . (  u1  . (  v0  . (!v1)))) + \
         ((  u0  . ((!u1) . ((!v0) . (!v1)))) + \
         ((  u0  . ((!u1) . (  v0  .   v1 ))) + \
          (  u0  . (  u1  . (  v0  . (!v1))))))))"

ltl_expr = 'G (F ((!v1) . (X v1)))'
#ltl_expr = 'G (F v1)'
solver = Solver()
ast = ast_to_nnf(parser.parse(ltl_expr))
def_vars = set()
ltl_looping_encode(0, 2, 4, ast, solver, def_vars)
#nonLooping(ast, 0, 3, solver, def_vars)
print(solver)

init_gen = parse_pred_z3_gen(init, 2)
trans_gen = parse_trans_z3_gen(trans, 2)

# upto 4 path
solver.add(init_gen([Bool('s_0_0'), Bool('s_0_1')]))
solver.add(trans_gen([Bool('s_0_0'), Bool('s_0_1')], [Bool('s_1_0'), Bool('s_1_1')]))
solver.add(trans_gen([Bool('s_1_0'), Bool('s_1_1')], [Bool('s_2_0'), Bool('s_2_1')]))
solver.add(trans_gen([Bool('s_2_0'), Bool('s_2_1')], [Bool('s_3_0'), Bool('s_3_1')]))
solver.add(trans_gen([Bool('s_3_0'), Bool('s_3_1')], [Bool('s_4_0'), Bool('s_4_1')]))

## Non looping condition
#for i in range(0, 4):
#    for j in range(0, i):
#        solver.add(Not(And( (Bool('s_%d_0'%i) == Bool('s_%d_0'%j)),
#                            (Bool('s_%d_1'%i) == Bool('s_%d_1'%j)))))
#

# loops back to 2
solver.add(Bool('s_2_0') == Bool('s_4_0'))
solver.add(Bool('s_2_1') == Bool('s_4_1'))

print(solver)

# Formula is true
solver.add(Bool('lp_%s_%d_%d_%d'%(ast.vp, 4, 0, 2)))

# Check
print(solver.check())
mdl = solver.model()
print(mdl)
trace_print(2, 5, mdl)
