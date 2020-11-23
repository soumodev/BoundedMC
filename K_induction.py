from reocc_diam import *

def K_induction(n,init,trans,p):
    j=k=get_reocc_diam(n,init,trans)
    S_N_prime = [[Bool("x_%s_%s" % (j-k,i+1)) for i in range(n)]]
    s=Solver()
    s.add(init(S_N_prime[0]))
    s.push()
    s.add(Not(p(S_N_prime[0])))
    if(s.check() == unsat):
        while(k>0):
            s.pop()
            print("Checking for CEX after %d transitions"%(j-k+1))
            S_N_prime.append([Bool("x_%s_%s" %(j-k+1,i+1)) for i in range(n)])
            s.add(trans(S_N_prime[j-k],S_N_prime[j-k+1]))
            s.push()
            s.add(Not(p(S_N_prime[j-k+1])))
            if(s.check() == sat):
                print(s.model())
                return "Invariant doesn't hold and there is a counterexample"
            k-=1
        return "The invariant holds!"
    else:
        print(s.model())
        return "Invariant doesn't hold and there is a counterexample"