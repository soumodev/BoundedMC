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
    return(s[0]==True)

def trans(s,s_p):
    return(s[0]==s_p[0])

def Invariant_Check(n,k,init,trans,p):
    S_0 = [Bool("x_%s" % (i+1)) for i in range(n)]
    s=Solver()
    s.add(init(S_0))
    s.add(Not(p(S_0)))
    s.push()
    if(s.check() == unsat):
        s.pop()
        S_N=S_0
        S_N_prime = [Int("x_%s_%s" %(i+1,k)) for i in range(n)]
        while(k!=0):
            s.add(trans(S_N,S_N_prime))
            s.add(Not(p(S_N_prime)))
            s.push()
            S_N=S_N_prime
            if(s.check == sat):
                print(s.model())
                return "Invariant doesn't hold and there is a counterexample"
            k-=1
            s.pop()
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
    st = [[Bool('s_0_%d'%i) for i in range(n_bits)], [Bool('s_1_%d'%i) for i in range(n_bits)]]

    # Add path conditions for lasso length 1
    s.add(And(init(st[0]), trans(st[0], st[1])))
    # Add cex conditions for lasso length 1
    s.add(And(Not(p(st[0])), Not(p(st[1]))))

    for k in range(1, threshold+1):
        # Set backtrack point before lasso constriant
        s.push()
        # Add lasso expr for k
        s.add(Or(And( Not(Xor(p, q)) for p, q in zip sti, st[k]) for sti in st[:-1]))
        # check if cex
        if s.check() == sat:
            print("Found CEX of length %d:"%k)
            print(s.model())
            return
        # remove lasso constraint
        s.pop()

        # Introduce new variables
        st.append([Bool('s_%d_%s'%(k+1, i)) for i in range(n_bits)])
        
        # Add path and cex conditions
        s.add(trans(st[k], st[k+1]))
        s.add(Not(p(st[k+1])))
        return "Invariant doesn't hold and there is a counterexample"
