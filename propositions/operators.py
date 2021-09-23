# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from __future__ import annotations

from dataclasses import dataclass
from functools import wraps  # Class-level lazy getter decorator

from propositions.semantics import *
from propositions.syntax import *


class LazyClassProperty:
    def __init__(self, wrapped_property):
        self._wrapped = wrapped_property
        try:
            # Duplicate its docstring if exists
            self.__doc__ = wrapped_property.__doc__
        except:  # pragma: no cover
            pass

    def __get__(self, inst, objtype=None):
        # ask the value from the wrapped object, giving it to our class
        val = self._wrapped(objtype)

        # set the attribute directly to the class, thereby
        # avoiding the descriptor to be called multiple times
        setattr(objtype, self._wrapped.__name__, val)

        # and return the calculated value
        return val


class TransformOperators:
    @LazyClassProperty
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

    @LazyClassProperty
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

    @LazyClassProperty
    def not_and(self) -> Dict[str, Formula]:
        return {BINARY_OR: ~(~Placeholder.first & ~Placeholder.second)}

    @LazyClassProperty
    def implies_not(self) -> Dict[str, Formula]:
        return {
            BINARY_AND: ~Formula(
                BINARY_IMPLY, Placeholder.first, ~Placeholder.second
            ),
            BINARY_OR: Formula(
                BINARY_IMPLY, ~Placeholder.first, Placeholder.second
            ),
        }

    @LazyClassProperty
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
    return formula.substitute_operators(TransformOperators.not_or_and)


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
        TransformOperators.not_or_and
    ).substitute_operators(TransformOperators.not_and)


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
        TransformOperators.not_or_and
    ).substitute_operators(TransformOperators.nand)


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
        TransformOperators.not_or_and
    ).substitute_operators(TransformOperators.implies_not)


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
        TransformOperators.not_or_and
    ).substitute_operators(TransformOperators.implies_false)
