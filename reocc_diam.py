"""
Defines functions to find the reoccurrence diameter of a given Kripke model.

Command line usage:
    python reocc_diam.py <specification_file>
"""

from z3 import *

def get_reocc_diam(n_bits, init, trans):
    """
    Given a Kripke model with `n_bits`, where `init` takes a list of z3 variables and returns a z3
    expression representing the initial states, and `trans` takes two lists of z3 variables and returns a
    z3 expression representing the transition relation, this function returns the reoccurrence
    diamter of the kripke model
    """

    s = Solver()

    # Introduce variables
    st = [[Bool('s_0_%d'%i) for i in range(n_bits)], [Bool('s_1_%d'%i) for i in range(n_bits)]]

    # Assert non repeating path of length 2
    s.add(And(init(st[0]), trans(st[0], st[1]), Or([ Xor(a, b) for a, b in zip(st[0], st[1]) ])))

    rd = 1
    while True:
        # Check if there is a non repeating path of length of rd+1
        if s.check() == unsat:
            return rd

        # Set up check for rd++
        rd += 1
        # Make new state
        st.append([Bool('s_%d_%d'%(rd,i)) for i in range(n_bits)])
        # New state belongs to a length rd path
        s.add(trans(st[rd-1], st[rd]))
        # New state is unique
        s.add(And([ Or([ Xor(a, b) for a, b in zip(sti, st[rd]) ]) for sti in st[:-1] ]))
        
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

    print("The reoccurrence diameter is %d"%get_reocc_diam(n_bits, init_z3_gen, trans_z3_gen))
