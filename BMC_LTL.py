from z3 import *
from ltl_encode import *
from utils import *


def BMC_LTL(n,threshold,init,trans,ast):
    """
    Given the ast of a ltl property, initial states, and transition relation, looks for a
    counterexample of size upto `threshold`. `n` is the number of bits.
    """
    # Initialize vars, solver and set.
    s_i = [[Bool('s_0_%d'%(i)) for i in range(n)]]
    s=Solver()
    mem=set()
    
    # Initialization constraint, we continue this to future iterations
    s.add(init(s_i[0]))
    
    # Collect the nonlooping condition
    no_loop = Not(False)

    # BMC loop
    for k in range(threshold):
        
        # Non looping case.
        print("Looking for non looping CEX of size %d"%(k+1), end = '\r')
        # We firstly add nonlooping condition, we can do it outside the push/pop
        # section, see ltl_encode.py for a breif explanation as to why. This will reduce the work
        # done in future encodings, and will hopefully reduce SAT call times, as the SAT solver does
        # not throw away clauses learnt from these constraints.
        nonLooping(ast,0,k,s,mem)
        s.push()
        # The no_loop constraint must be added inside the push/pop section, and so must be the
        # constraint asserting that the formula is true. Otherwise, an unsat result will propagate
        # to all future SAT calls
        s.add(no_loop)
        s.add(Bool('nl_%s_%d_0'%(ast.vp,k)))
        # Check sat, print CEX
        if s.check() == sat:
            print("FOUND non looping CEX of size %d:                                               "%(k+1))
            trace_print(n,k+1,s.model())
            return
        s.pop()

        # Looping case. We do one sat call for each looping position. Similar to before, we carry
        # over the looping encode constraints and put the looping constraint, and the actual formula
        # satisfaction constraint inside a push/pop section. 
        for l in range(k):
            print("Looking for looping CEX of size %d with last state equal to state at %d"%(k+1, l), 
                        end = '\r')
            ltl_looping_encode(0,l,k,ast,s,mem)
            s.push()
            s.add( And([ s_i[l][i] == s_i[k][i] for i in range(n) ]))
            s.add(Bool('lp_%s_%d_0_%d'%(ast.vp,k,l)))
            if s.check() == sat:
                print("FOUND looping CEX of size %d with last state equal to state at %d:          "%(k+1, l))
                #print(s) # DEBUG
                trace_print(n,k+1,s.model())
                return
            s.pop()

        # Create new vars for next k, update path constraints, and update the non_looping
        # constraint.
        s_i.append([Bool('s_%d_%d'%(k+1,i)) for i in range(n)])
        s.add(trans(s_i[k],s_i[k+1]))
        no_loop = And(no_loop,And([ Not( And([ s_i[k+1][i] == s_i[j][i] for i in range(n) ]))
                                                    for j in range(k+1) ]))

    print("Could not find CEX paths of length less than %d long.                                  "%threshold)


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

#prop = 'G (F (((!v1) . v0) . (X v1)))'
prop = 'G (F (v1 . (v0 U ((!v0) . (!v1)))))'
#prop = 'fls'

BMC_LTL(2, 100, parse_pred_z3_gen(init, 2), parse_trans_z3_gen(trans, 2),
        ast_to_nnf(parser.parse(prop)))
