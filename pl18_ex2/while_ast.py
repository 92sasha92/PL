"""
AST (Abstract Syntax Tree) classes for While language
"""


# Abstract Classes

class AST(object):
    pass

class Expr(AST):
    pass

class ArithExpr(Expr):
    pass

class BoolExpr(Expr):
    pass

class Statement(AST):
    pass


# Statements

class Skip(Statement):
    def __repr__(self):
        return 'Skip()'
    def __str__(self):
        return 'skip'

class Assign(Statement):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs
    def __repr__(self):
        return 'Assign({}, {})'.format(self.lhs, self.rhs)
    def __str__(self):
        return '{} := {}'.format(self.lhs, self.rhs)

class Comp(Statement):
    def __init__(self, S1, S2):
        self.S1 = S1
        self.S2 = S2
    def __repr__(self):
        return 'Comp({}, {})'.format(self.S1, self.S2)
    def __str__(self):
        return '{} ; {}'.format(self.S1, self.S2)

class If(Statement):
    def __init__(self, b, S1, S2):
        self.b = b
        self.S1 = S1
        self.S2 = S2
    def __repr__(self):
        return 'If({}, {}, {})'.format(self.b, self.S1, self.S2)
    def __str__(self):
        return 'if ({}) then ({}) else ({})'.format(self.b, self.S1, self.S2)

class While(Statement):
    def __init__(self, b, S):
        self.b = b
        self.S = S
    def __repr__(self):
        return 'While({}, {})'.format(self.b, self.S)
    def __str__(self):
        return 'while ({}) do ({})'.format(self.b, self.S)

#
# --- ADD HERE IN QUESTION 3 ---
#


# Arithmetic Expressions

class ALit(ArithExpr):
    def __init__(self, value):
        self.value = value
    def __repr__(self):
        return 'ALit({})'.format(self.value)
    def __str__(self):
        return str(self.value)

class Var(ArithExpr):
    def __init__(self, var_name):
        self.var_name = var_name
    def __repr__(self):
        return 'Var({})'.format(self.var_name)
    def __str__(self):
        return self.var_name

class Plus(ArithExpr):
    def __init__(self, a1, a2):
        self.a1 = a1
        self.a2 = a2
    def __repr__(self):
        return 'Plus({}, {})'.format(self.a1, self.a2)

class Times(ArithExpr):
    def __init__(self, a1, a2):
        self.a1 = a1
        self.a2 = a2
    def __repr__(self):
        return 'Times({}, {})'.format(self.a1, self.a2)

class Minus(ArithExpr):
    def __init__(self, a1, a2):
        self.a1 = a1
        self.a2 = a2
    def __repr__(self):
        return 'Minus({}, {})'.format(self.a1, self.a2)

#
# --- ADD HERE IN QUESTION 1 ---
#

class BitAnd(ArithExpr):
    def __init__(self, a1, a2):
        self.a1 = a1
        self.a2 = a2
    def __repr__(self):
        return 'BitAnd({}, {})'.format(self.a1, self.a2)

class BitShiftLeft(ArithExpr):
    def __init__(self, a1, a2):
        self.a1 = a1
        self.a2 = a2
    def __repr__(self):
        return 'BitShiftLeft({}, {})'.format(self.a1, self.a2)

class BitShiftRight(ArithExpr):
    def __init__(self, a1, a2):
        self.a1 = a1
        self.a2 = a2
    def __repr__(self):
        return 'BitShiftRight({}, {})'.format(self.a1, self.a2)


# Boolean Expressions

class BLit(ArithExpr):
    def __init__(self, value):
        self.value = value
    def __repr__(self):
        return 'BLit({})'.format(self.value)

class Eq(BoolExpr):
    def __init__(self, a1, a2):
        self.a1 = a1
        self.a2 = a2
    def __repr__(self):
        return 'Eq({}, {})'.format(self.a1, self.a2)

class LE(BoolExpr):
    def __init__(self, a1, a2):
        self.a1 = a1
        self.a2 = a2
    def __repr__(self):
        return 'LE({}, {})'.format(self.a1, self.a2)

class Not(BoolExpr):
    def __init__(self, b):
        self.b = b
    def __repr__(self):
        return 'Not({})'.format(self.b)

class And(BoolExpr):
    def __init__(self, b1, b2):
        self.b1 = b1
        self.b2 = b2
    def __repr__(self):
        return 'And({}, {})'.format(self.b1, self.b2)

class Or(BoolExpr):
    def __init__(self, b1, b2):
        self.b1 = b1
        self.b2 = b2
    def __repr__(self):
        return 'Or({}, {})'.format(self.b1, self.b2)
