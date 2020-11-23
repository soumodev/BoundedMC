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
def Invariant_Check(n,k,init,trans,p):
    S_0 = [Bool("x_%s" % (i+1)) for i in range(n)]
    s=Solver()
    s.add(init(S_0), Not(p(S_0)))
    if(s.check() == unsat):
        S_N=S_0
        while(k!=0):
            S_N_prime = [Int("x_%s_%s" %(i+1,k)) for i in range(n)]
            solver,S_N_p = trans(n,S_N)
            for i in range(n):
                solver.add(S_N_prime[i]==S_N_p[i])
            solver.add(Not(p(S_N_prime)))
            if(solver.check == sat):
                print(solver.model())
                return "Invariant doesn't hold and there is a counterexample"
            k-=1
        return "The invariant holds"
    elif(s.check() == sat):
        print(s.model())
        return "Invariant doesn't hold and there is a counterexample"
