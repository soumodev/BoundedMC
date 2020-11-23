from z3 import *
#the Kripke encoding
def init(s):
    return(And(s[0],Not(s[1])))

def p(s):
    return(s[0]==False)

def trans(n,s):
    s_prime = [Bool("y_%s" % (i+1)) for i in range(n)] 
    s1 = Solver()
    s1.add(Xor(s[0],s_prime[0]))
    return s1,s_prime

#the code for checking invariant
def init(s):
    return(And(s[0],Not(s[1])))

def p(s):
    return(s[0]==False)

def trans(s,s_p):
    return(s[0]==s_p[0])

def Invariant_Check(n,k,init,trans,p):
    S_0 = [Bool("x_%s" % (i+1)) for i in range(n)]
    s=Solver()
    s.add(init(S_0),Not(p(S_0)))
    if(s.check() == unsat):
        s.reset()
        S_N=S_0
        S_N_prime = [Int("x_%s_%s" %(i+1,k)) for i in range(n)]
        while(k!=0):
            s.add(trans(S_N,S_N_prime), Not(p(S_N_prime)))
            S_N=S_N_prime
            if(s.check == sat):
                print(s.model())
                return "Invariant doesn't hold and there is a counterexample"
            k-=1
            s.reset()
        return "The invariant holds"
    else:
        print(s.model())
        return "Invariant doesn't hold and there is a counterexample"

# BMC for Fp
def Invariant_Check_Fp(n_bits, threshold, init, trans, p):
    """
    Check if there are lassoing cex to Fp of length less than threshold
    """
    s = Solver()

    # The variables for the states
    st = [[Bool('s_0_%i'%i) for i in range(n_bits)]]

    # This will hold init(s0) /\ T(s0, s1)....
    trace_expr = init(st[0])
    # This will hold ~p(s0) /\ ...
    pred_not_expr = Not(p(st[0]))
    for k in range(threshold+1):
        s.push()
        lasso_expr = Or(And( Not(Xor(p, q)) for p, q in zip sti, st[k])
