# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from dataclasses import dataclass

from propositions.semantics import *
from propositions.syntax import *


@dataclass
class Placeholder:
    first: str = "p"
    second: str = "q"


def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5
    apply_allowed_binary_op: Dict[str, Formula] = {
        BINARY_NOR: ~Formula(Placeholder.first) & ~Formula(Placeholder.second),
        BINARY_NAND: ~Formula(Placeholder.first) | ~Formula(Placeholder.second),
        BINARY_XOR: (~Formula(Placeholder.first) & Formula(Placeholder.second))
        | (Formula(Placeholder.first) & ~Formula(Placeholder.second)),
        FALSE_OP: Formula(Placeholder.first) & ~Formula(Placeholder.first),
        TRUE_OP: Formula(Placeholder.first) | ~Formula(Placeholder.first),
    }
    logical_same_formula: Formula = ~apply_allowed_binary_op[
        BINARY_XOR
    ]  # require being the same formula using logics

    apply_allowed_binary_op.update(
        {
            BINARY_IMPLY: ~Formula(Placeholder.first) | logical_same_formula,
            BINARY_IFF: (~Formula(Placeholder.first) | logical_same_formula)
            & (~Formula(Placeholder.second) | logical_same_formula),
        }
    )

    allowed_ops: Set[str] = {BINARY_AND, BINARY_OR, NEGATE_SYM}
    formula_operators: Set[str] = formula.operators()
    subtitution_map: Dict[str, Formula] = {
        op: apply_allowed_binary_op[op]
        for op in formula_operators
        if op not in allowed_ops
    }
    return formula.substitute_operators(subtitution_map)


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
