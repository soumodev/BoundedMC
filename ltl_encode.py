"""
Define functions to encode the expression for a k-long counterexample to an arbitrary LTL formula in
SMT.
"""

def ltl_looping(start_pos, loop_pos, length, ast):
    """
    Given the `ast` of a formula, returns a z3 expression representing the partial looping translation of
    the formula starting at the position `start_pos` (i in the lecture notation), for a path of
    length `length` (k) looping at the position `loop_pos` (l), according to the recursive relation
    given in class. To make sure that the resulting formula is polynomial in the length of the path,
    we must introduce a number of intermediate variables representing the translation of each
    formula and 
    """

