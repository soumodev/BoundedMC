# USAGE

```python

from ply_parser import *

tree = parser.parse("AG ((a ^ (EX (AF (AX (tru AU (EG fls)))))) EU ((EF d) . (b + (! c))))")
print(tree)

# for monadic:

print(tree.child)
print(tree.child.type)

# for dyadic:

print(tree.child.left)
print(tree.child.left.type)
print(tree.child.right.type)
print(tree.child.right.type)

```

The parser was changed for usage with LTL operators.
