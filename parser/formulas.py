# from z3 import *

#Could simply use namedtuples from collections instead if making these classes by hand.
class Formula():
  def __str__(self):
    return str( self.to_tuple())

class FormulaMonadic(Formula): #Note that even ('PROP','p') is of type monadic
  def __init__(self, typ, child):
    self.type = typ
    self.child = child
    # A string that is unique for the expr represented
    self.vp = "b_%s_%s_c"%(typ, child.vp if isinstance(child, Formula) else child)
    self.size = 1 + (self.child.size if isinstance(child, Formula) else 0)

  def to_tuple(self):
    if self.type in ['PROP', 'NEGPROP', 'LITERAL']: # NOTE: NEGPROP is not a token, just a special
                                                    #       ast node type for nnf forms
      return (self.type, self.child)
    return (self.type, self.child.to_tuple())

class FormulaDyadic(Formula):
  def __init__(self, typ, left, right):
    self.type = typ
    self.left = left
    self.right = right
    # A string that is unique for the expr represented
    self.vp = "b_%s_%s_%s_c"%(typ, left.vp if isinstance(left, Formula) else left,
                                    right.vp if isinstance(right, Formula) else right)
    self.size = 1 + (self.left.size  if isinstance(left,  Formula) else 0) \
                  + (self.right.size if isinstance(right, Formula) else 0)

  def to_tuple(self):
    if self.type in ['PROP', 'NEGPROP', 'LITERAL']:
      return (self.type, self.child)
    return (self.type, self.left.to_tuple(), self.right.to_tuple())

# ----- Test -----

# print FormulaDyadic('U', FormulaMonadic('PROP', 'p'), FormulaMonadic('PROP', 'p'))
# print FormulaMonadic('PROP', 'p')

# print nnf(FormulaDyadic('U', FormulaMonadic('PROP', 'p'), FormulaMonadic('PROP', 'p')))
# print nnf(FormulaMonadic('NOT', FormulaMonadic('PROP', 'p')))
