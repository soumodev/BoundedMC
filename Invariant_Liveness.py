"""
BMC loop for safety and simple liveness properties, that is, properties of the form Fp and Gp, where
p has no LTL operators.

Command line usage:
    python Invariant_Liveness.py <spec_file> [threshold]

    Check the specificiation given in the file `spec_file`. If `threshold` is provided, run BMC loop
    upto the given threshold, else use the reoccurrence diameter as the threshold
"""

from z3 import *
from utils import *

#the code for checking invariant
def Invariant_Check_Gp(n,k,init,trans,p):
    """
    Check if there are lassoing cex to `Gp` of length less than `k`. The given kripke model
    has `n` bits, `init` takes a list of z3 variables and returns a z3 expression representing
    the initial states, `trans` takes two lists of z3 variables and returns a z3 expression
    representing the transition relation.
    """
    j=k
    S_N_prime = [[Bool("s_%d_%d" % (j-k,i)) for i in range(n)]]
    s=Solver()
    s.add(init(S_N_prime[0]))
    s.push()
    s.add(Not(p(S_N_prime[0])))
    if(s.check() == unsat):
        while(k>0):
            s.pop()
            print("Checking for CEX after %d transitions"%(j-k+1), end='\r')
            S_N_prime.append([Bool("s_%d_%d" %(j-k+1,i)) for i in range(n)])
            s.add(trans(S_N_prime[j-k],S_N_prime[j-k+1]))
            s.push()
            s.add(Not(p(S_N_prime[j-k+1])))
            # DEBUG
            #print("SAT call:")
            #print(s.assertions())
            if(s.check() == sat):
                print("Invariant doesn't hold and there is a counterexample             ")
                trace_print(n, len(S_N_prime), s.model())
                #print(s.model()) # DEBUG
                return
            k-=1
        print("Found no counterexamples within threshold                                ")
        return
    else:
        print("Invariant doesn't hold and there is a counterexample                     ")
        trace_print(n, 1, s.model())
        #print(s.model()) # DEBUG
        return

#BMC for Fp
def Invariant_Check_Fp(n_bits, threshold, init, trans, p):
    """
    Check if there are lassoing cex to `Fp` of length less than `threshold`. The given kripke model
    has `n_bits` bits, `init` takes a list of z3 variables and returns a z3 expression representing
    the initial states, `trans` takes two lists of z3 variables and returns a z3 expression
    representing the transition relation.
    """
    s = Solver()

    # The variables for the states
    st = [[Bool('s_0_%d'%i) for i in range(n_bits)], [Bool('s_1_%d'%i) for i in range(n_bits)]]

    # Add path conditions for lasso length 1
    s.add(And(init(st[0]), trans(st[0], st[1])))
    # Add cex conditions for lasso length 1
    s.add(And(Not(p(st[0])), Not(p(st[1]))))

    for k in range(1, threshold+1):
        # DEBUG
        print("Looking for cex of size %d"%k, end='\r')

        # Check for each loop position
        for i in range(k):
            # Set backtrack point before lasso constriant
            s.push()
            # Add lasso position
            s.add(And([ p == q for p, q in zip (st[i], st[k]) ]))
            # check if cex
            if s.check() == sat:
                print("Found CEX of length %d with last state being the same as %d         "%(k, i))
                trace_print(n_bits, k+1, s.model(), i)
                return
            # remove lasso constraint
            s.pop()

        # Introduce new variables
        st.append([Bool('s_%d_%d'%(k+1, i)) for i in range(n_bits)])
        
        # Add path and cex conditions
        s.add(trans(st[k], st[k+1]))
        s.add(Not(p(st[k+1])))

    print("Found no counterexamples within the threshold")


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

    # Get threshold
    if len(sys.argv) >= 3:
        threshold = int(sys.argv[2])
    else:
        from reocc_diam import *
        threshold = get_reocc_diam(n_bits, init_z3_gen, trans_z3_gen)
        print('Using reoccurrence diameter %d as threshold'%threshold)

    # Parse and check properties
    for prop_str in prop_strs:
        print('Checking property %s:'%prop_str)
        prop_ast = parser.parse(prop_str)
        if prop_ast.type == 'F':
            print('Property is a simple liveness property')
            Invariant_Check_Fp(n_bits, threshold, init_z3_gen, trans_z3_gen, 
                                parse_pred_z3_gen(prop_ast.child, n_bits))
        elif prop_ast.type == 'G':
            print('Property is a simple safety property')
            Invariant_Check_Gp(n_bits, threshold, init_z3_gen, trans_z3_gen, 
                                parse_pred_z3_gen(prop_ast.child, n_bits))
        else:
            print('Property is not of Fp or Gp form, ignoring')
