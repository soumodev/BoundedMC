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
            print("Checking for CEX after %d transitions"%(j-k+1))
            S_N_prime.append([Bool("s_%d_%d" %(j-k+1,i)) for i in range(n)])
            s.add(trans(S_N_prime[j-k],S_N_prime[j-k+1]))
            s.push()
            s.add(Not(p(S_N_prime[j-k+1])))
            # DEBUG
            #print("SAT call:")
            #print(s.assertions())
            if(s.check() == sat):
                print("Invariant doesn't hold and there is a counterexample")
                trace_print(n, len(S_N_prime), s.model())
                #print(s.model()) # DEBUG
                return
            k-=1
        print("Found no counterexamples within threshhold")
        return
    else:
        print("Invariant doesn't hold and there is a counterexample")
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
        print("Looking for cex of size %d"%k)

        # Set backtrack point before lasso constriant
        s.push()
        # Add lasso expr for k
        s.add(Or([ And([ Not(Xor(p, q)) for p, q in zip (sti, st[k]) ]) for sti in st[:-1] ]))
        # check if cex
        if s.check() == sat:
            print("Found CEX of length %d:"%k)
            trace_print(n_bits, k+1, s.model())
            return
        # remove lasso constraint
        s.pop()

        # Introduce new variables
        st.append([Bool('s_%d_%d'%(k+1, i)) for i in range(n_bits)])
        
        # Add path and cex conditions
        s.add(trans(st[k], st[k+1]))
        s.add(Not(p(st[k+1])))

    print("Found no counterexamples within the threshold")

# DEBUG
from parse_to_z3 import *

n_bits = 2
init = "((!v0) . (!v1))"
trans = "(((!u0) . ((!u1) . ((!v0) .   v1))) + \
         (((!u0) . (  u1  . (  v0  . (!v1)))) + \
         ((  u0  . ((!u1) . ((!v0) . (!v1)))) + \
         ((  u0  . ((!u1) . (  v0  .   v1 ))) + \
          (  u0  . (  u1  . (  v0  . (!v1))))))))"
pred = "(v0 . v1)"

Invariant_Check_Fp(n_bits, 5, parse_pred_z3_gen(init, n_bits), parse_trans_z3_gen(trans, n_bits),
        parse_pred_z3_gen(pred, n_bits))
Invariant_Check_Gp(n_bits, 5, parse_pred_z3_gen(init, n_bits), parse_trans_z3_gen(trans, n_bits),
        parse_pred_z3_gen("((!v0) + (!v1))", n_bits))

