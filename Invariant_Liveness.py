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