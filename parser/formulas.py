# from z3 import *

#Could simply use namedtuples from collections instead if making these classes by hand.
class Formula():     
  def __str__(self):
    return str( self.to_tuple())

class FormulaMonadic(Formula): #Note that even ('PROP','p') is of type monadic
  def __init__(self, typ, child):
    self.type = typ
    self.child = child

  def to_tuple(self):
    if self.type in ['PROP', 'LITERAL']:
      return (self.type, self.child)
    return (self.type, self.child.to_tuple())

class FormulaDyadic(Formula):
  def __init__(self, typ, left, right):
    self.type = typ
    self.left = left
    self.right = right

  def to_tuple(self):
    if self.type in ['PROP', 'LITERAL']:
      return (self.type, self.child)
    return (self.type, self.left.to_tuple(), self.right.to_tuple())

# ----- Test -----

# print FormulaDyadic('U', FormulaMonadic('PROP', 'p'), FormulaMonadic('PROP', 'p'))
# print FormulaMonadic('PROP', 'p')

# print nnf(FormulaDyadic('U', FormulaMonadic('PROP', 'p'), FormulaMonadic('PROP', 'p')))
# print nnf(FormulaMonadic('NOT', FormulaMonadic('PROP', 'p')))
