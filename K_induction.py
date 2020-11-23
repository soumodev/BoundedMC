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
            print("Checking for CEX after %d transitions"%(k))
            S_N_prime.append([Bool("s_%s_%s" % (k,i)) for i in range(n)])
            s.add(And(p(S_N_prime[k-1]),trans(S_N_prime[k-1],S_N_prime[k])))
            s.push()
            #print(s) #DEBUG
            s.add(Not(p(S_N_prime[k])))
            if(s.check()==unsat):
                print("Verified, p is %d-inductive"%k)
                return
            s1.pop()
            s1.add(trans(S_N_prime[k-1],S_N_prime[k]))
            s1.push()
            s1.add(Not(p(S_N_prime[k])))
            if(s1.check()==sat):
                print("CounterExample")
                trace_print(n, len(S_N_prime), s.model())
                return
            k+=1
        return "The invariant holds!"
    else:
        print("Invariant doesn't hold and there is a counterexample")
        trace_print(n, 1, s.model())
        return


# DEBUG
from parse_to_z3 import *

n_bits = 2
init = "((!v0) . (!v1))"
trans = "(((!u0) . ((!u1) . ((!v0) .   v1))) + \
         (((!u0) . (  u1  . (  v0  . (!v1)))) + \
         ((  u0  . ((!u1) . ((!v0) . (!v1)))) + \
         ((  u0  . ((!u1) . (  v0  .   v1 ))) + \
          (  u0  . (  u1  . (  v0  . (!v1))))))))"
pred = "!(v0 . v1)"

K_induction(n_bits, parse_pred_z3_gen(init, n_bits), parse_trans_z3_gen(trans, n_bits),
        parse_pred_z3_gen(pred, n_bits))
K_induction(n_bits, parse_pred_z3_gen(init, n_bits), parse_trans_z3_gen(trans, n_bits),
        parse_pred_z3_gen("tru", n_bits))

