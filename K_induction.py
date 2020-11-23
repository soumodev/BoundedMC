from reocc_diam import *

def K_induction(n,init,trans,p):
    S_N_prime = [[Bool("x_%s_%s" % (0,i+1)) for i in range(n)]]
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
            print("Checking for CEX after %d transitions"%(k))
            S_N_prime.append([Bool("x_%s_%s" % (k,i+1)) for i in range(n)])
            s.add(And(p(S_N_prime[k-1]),trans(S_N_prime[k-1],S_N_prime[k])))
            s.push()
            print(s)
            s.add(Not(p(S_N_prime[k])))
            if(s.check()==unsat):
                return "Verified"
            s1.pop()
            s1.add(trans(S_N_prime[k-1],S_N_prime[k]))
            s1.push()
            s1.add(Not(p(S_N_prime[k])))
            if(s1.check()==sat):
                return "CounterExample"
            k+=1
        return "The invariant holds!"
    else:
        print(s.model())
        return "Invariant doesn't hold and there is a counterexample"
