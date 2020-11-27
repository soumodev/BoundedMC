# Specification syntax:

## LTL Properties:

LTL properties are specified according to the syntax of the parser given for CTL. We have modified
the syntax of the parser by replacing the CTL operators with LTL operators, but all other aspects
are the same.

The sate space is assumed to be described by a collection of bits, and for each of these bits we
have a boolean variable that denotes that bit being `1`. The allowed variable names within
property specifications are of the form `vi`, which refers to the proposition that the `i`-th bit is
`1`.

## Initial Condition:

The initial condition is specified exactly like a LTL property, but no LTL operators are allowed,
and only the propositional operators like `+`, `.` and `!` are allowed. The conventions for variable
naming are same as that for LTL properties.

## Transition Relation:

The transition relation syntax is exacly like that of the inital condition, except now there are two
sets of allowed varaibles. In the expression for `R(u, v)` representing a transition from the state
`u` to the state `v`, the variables `ui` and `vi` represent the proposition that the `i`-th bit is
`1` in the state `u` and `v` respectively.

## Specification File:

The specification file is a text file with a python 4-tuple. The first element of this tuple is a
int giving us the number of bits in the description for the states. The second element is a string
for the initial condition in the syntax described above, and the third is a string for the
transition relation. Finally, the fourth element is a python list, each element of which is a string
in the above syntax specifying an LTL property. Thus,

```
(n_bits, inital, transition, [property1, property2, ... ])
```

Note that all the tasks use the same syntax for the specification file, but only work on properties
of certain specific forms.

# Using the scripts:

## Task 1:

The BMC loops for simple safety and liveness are given in the script `Invariant_Liveness.py`. The
command line usage is:

```
python Invariant_Liveness.py <spec_file> [threshold]
```

It checks all ltl properties in the given file of the form `Fp` or `Gp`, where `p` does not contain
any LTL operators by running a BMC loop upto the threshold. If the optional second second argument for
the threshold is not given, it uses the reoccurrence diameter as the threshold. 

## Task 2:

The script `reocc_diam.py` defines functions to calculate the reoccurrence diameter. The command
line usage is:

```
python reocc_diam.py <spec_file>
```

It ignores the properties in the specification file, and prints out the reoccurrence diameter of the
given system.

## Task 3:
 
The script `K_induction.py` performs k-induction on simple safety properties. The command line
usage is:

```
python K_induction.py <spec_file>
```

It checks all ltl properties in the given file of the form `Gp`, where `p` does not contain
any LTL operators using k-induction.

## Task 4:

The BMC loops for arbitrary LTL properties are given in the script `Invariant_Liveness.py`. The
command line usage is:

```
python Invariant_Liveness.py <spec_file> [threshold]
```

It checks all ltl properties in the given file by running a BMC loop upto the threshold. If the
optional second second argument for the threshold is not given, it uses the bound of the size of the
product system as given in the tableu method for the threshold. This is an exponential bound given
by `(2^n_bits)*(2^property_size)`.


