# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from __future__ import annotations

from dataclasses import dataclass
from functools import wraps  # lazy getter decorator

from propositions.semantics import *
from propositions.syntax import *


def lazyprop(op):
    transform_to: str = "to_" + op.__name__

    @property
    @wraps(op)
    def _memoize_op(self):
        if not hasattr(self, transform_to):
            setattr(self, transform_to, op(self))
        return getattr(self, transform_to)

    return _memoize_op


class TransformOperators:
    @lazyprop
    def not_or_and(self) -> Dict[str, Formula]:
        return {
            BINARY_IMPLY: Formula.parse("(~p|q)"),
            BINARY_XOR: Formula.parse("((p&~q)|(~p&q))"),
            BINARY_IFF: Formula.parse("((p&q)|(~p&~q))"),
            BINARY_NAND: Formula.parse("~(p&q)"),
            BINARY_NOR: Formula.parse("~(p|q)"),
            TRUE_OP: Formula.parse("(p|~p)"),
            FALSE_OP: Formula.parse("(p&~p)"),
        }

    @lazyprop
    def nand(self) -> Dict[str, Formula]:
        return {
            BINARY_OR: Formula(
                BINARY_NAND,
                Formula(BINARY_NAND, Placeholder.first, Placeholder.first),
                Formula(BINARY_NAND, Placeholder.second, Placeholder.second),
            ),
            BINARY_AND: Formula(
                BINARY_NAND,
                Formula(BINARY_NAND, Placeholder.first, Placeholder.second),
                Formula(BINARY_NAND, Placeholder.first, Placeholder.second),
            ),
            NEGATE_SYM: Formula(
                BINARY_NAND, Placeholder.first, Placeholder.first
            ),
        }

    @lazyprop
    def not_and(self) -> Dict[str, Formula]:
        return {BINARY_OR: ~(~Placeholder.first & ~Placeholder.second)}

    @lazyprop
    def implies_not(self) -> Dict[str, Formula]:
        return {
            BINARY_AND: ~Formula(
                BINARY_IMPLY, Placeholder.first, ~Placeholder.second
            ),
            BINARY_OR: Formula(
                BINARY_IMPLY, ~Placeholder.first, Placeholder.second
            ),
        }

    @lazyprop
    def implies_false(self) -> Dict[str, Formula]:
        return {
            NEGATE_SYM: Formula(
                BINARY_IMPLY, Placeholder.first, Formula(FALSE_OP)
            ),
            BINARY_OR: Formula(
                BINARY_IMPLY,
                Formula(BINARY_IMPLY, Placeholder.first, Formula(FALSE_OP)),
                Placeholder.second,
            ),
            BINARY_AND: Formula(
                BINARY_IMPLY,
                Formula(
                    BINARY_IMPLY,
                    Placeholder.first,
                    Formula(
                        BINARY_IMPLY, Placeholder.second, Formula(FALSE_OP)
                    ),
                ),
                Formula(FALSE_OP),
            ),
        }


@dataclass
class Placeholder:
    first: Formula = Formula("p")
    second: Formula = Formula("q")


transform_operators_to: TransformOperators = TransformOperators()


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
    return formula.substitute_operators(transform_operators_to.not_or_and)


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
    return formula.substitute_operators(
        transform_operators_to.not_or_and
    ).substitute_operators(transform_operators_to.not_and)


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
    return formula.substitute_operators(
        transform_operators_to.not_or_and
    ).substitute_operators(transform_operators_to.nand)


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
    return formula.substitute_operators(
        transform_operators_to.not_or_and
    ).substitute_operators(transform_operators_to.implies_not)


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
    return formula.substitute_operators(
        transform_operators_to.not_or_and
    ).substitute_operators(transform_operators_to.implies_false)
