"""

Semantics of arithmetic and boolean expressions.

Implemented according to
http://www.daimi.au.dk/~bra8130/Wiley_book/wiley.pdf (the book).

"""

from while_ast import *


tt = 'tt'
ff = 'ff'


def eval_arith_expr(e, s):
    """
    Semantics of arithmetic expressions.

    Implements Table 1.1 from the book.

    --- MODIFY THIS FUNCTION IN QUESTION 1 ---

    """

    if type(e) is ALit:
        return e.value

    elif type(e) is Var:
        return s[e.var_name]

    elif type(e) is Plus:
        return eval_arith_expr(e.a1, s) + eval_arith_expr(e.a2, s)

    elif type(e) is Times:
        return eval_arith_expr(e.a1, s) * eval_arith_expr(e.a2, s)

    elif type(e) is Minus:
        return eval_arith_expr(e.a1, s) - eval_arith_expr(e.a2, s)

    elif type(e) is BitAnd:
        return eval_arith_expr(e.a1, s) & eval_arith_expr(e.a2, s)

    elif type(e) is BitShiftLeft:
        return eval_arith_expr(e.a1, s) << eval_arith_expr(e.a2, s)

    elif type(e) is BitShiftRight:
        return eval_arith_expr(e.a1, s) >> eval_arith_expr(e.a2, s)

    else:
        assert False # Error


def convert_python_bool_expr_to_tt_or_ff(b):
    if b is True:
        return tt

    if b is False:
        return ff

    print "b is " + b
    assert False  # Error


def eval_bool_expr(e, s):
    """
    Semantics of arithmetic expressions

    Implements Table 1.2 from the book.

    --- MODIFY THIS FUNCTION IN QUESTION 1 ---

    """

    if type(e) is BLit:
        return convert_python_bool_expr_to_tt_or_ff(e.value)

    elif type(e) is Eq:
        return convert_python_bool_expr_to_tt_or_ff(eval_arith_expr(e.a1, s) == eval_arith_expr(e.a2, s))

    elif type(e) is LE:
        return convert_python_bool_expr_to_tt_or_ff(eval_arith_expr(e.a1, s) <= eval_arith_expr(e.a2, s))

    elif type(e) is Not:
        rVal = eval_bool_expr(e.b, s)
        if rVal is ff:
            return tt

        if rVal is tt:
            return ff

        assert False  # Error


    elif type(e) is And:
        rVal1 = eval_bool_expr(e.b1, s)
        if rVal1 is ff:
            return ff

        rVal2 = eval_bool_expr(e.b2, s)
        if rVal2 is ff:
            return ff

        return tt

    elif type(e) is Or:
        rVal1 = eval_bool_expr(e.b1, s)
        if rVal1 is tt:
            return tt

        rVal2 = eval_bool_expr(e.b2, s)
        if rVal2 is tt:
            return tt

        return ff


    else:
        assert False # Error


if __name__ == '__main__':
    # (x + 1) * (x - 1)
    a = Times(Plus(Var('x'), ALit(1)), Minus(Var('x'), ALit(1)))

    print a
    print eval_arith_expr(a, {'x':10})
    print

    b = And(LE(ALit(1), ALit(2)),
            Not(BLit(False)))

    print b
    print eval_bool_expr(b, {'x':10})
    print

    c = BitAnd(BitShiftLeft(ALit(2), ALit(1)), BitShiftRight(ALit(16), ALit(2)))

    print c
    print eval_arith_expr(c, {})
    print

    #
    # --- ADD MORE TESTS HERE ---
    #
