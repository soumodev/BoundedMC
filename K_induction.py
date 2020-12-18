"""
Uses k-induction to check for the correctness of simple safety properties. Properties must be of the
form Gp, where p has no LTL operators.

Command line usage:
    python K_induction.py <specification_file>
"""
from z3 import *
from utils import *

def K_induction(n,init,trans,p):
    S_N_prime = [[Bool("s_%s_%s" % (0,i)) for i in range(n)]]
    s=Solver()
    s1=Solver()
    s.push()
    s1.add(init(S_N_prime[0]))
    s1.push()
    s1.add(Not(p(S_N_prime[0])))
    if(s1.check() == unsat):
        k=1
        while(True):
            s.pop()
            print("Checking for CEX after %d transitions"%(k), end='\r')
            S_N_prime.append([Bool("s_%s_%s" % (k,i)) for i in range(n)])
            s.add(And(p(S_N_prime[k-1]),trans(S_N_prime[k-1],S_N_prime[k])))
            s.push()
            s.add(Not(p(S_N_prime[k])))
            if(s.check()==unsat):
                print("Verified, p is %d-inductive                                          "%k)
                return
            s1.pop()
            s1.add(trans(S_N_prime[k-1],S_N_prime[k]))
            s1.push()
            s1.add(Not(p(S_N_prime[k])))
            if(s1.check()==sat):
                print("CounterExample                                                       ")
                trace_print(n, len(S_N_prime), s.model())
                return
            k+=1
        print("The invariant could not be proved                                            ")
    else:
        print("Invariant doesn't hold and there is a counterexample                         ")
        trace_print(n, 1, s.model())
        return


if __name__ == "__main__":
    
    import sys
    from parse_to_z3 import *
    from parser.ply_parser import *
    from parser.formulas import *

    # Read spec file
    n_bits, init_str, trans_str, prop_strs = 0, '', '', []
    with open(sys.argv[1]) as f:
        n_bits, init_str, trans_str, prop_strs = eval(f.read())
    
    # Parse system
    init_z3_gen = parse_pred_z3_gen(init_str, n_bits)
    trans_z3_gen = parse_trans_z3_gen(trans_str, n_bits)

    # Parse and check properties
    for prop_str in prop_strs:
        print('Checking property %s:'%prop_str)
        prop_ast = parser.parse(prop_str)
        if prop_ast.type == 'G':
            K_induction(n_bits, init_z3_gen, trans_z3_gen, parse_pred_z3_gen(prop_ast.child, n_bits))
        else:
            print('Property is not of Gp form, ignoring')
