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
    first: Formula = Formula("p")
    second: Formula = Formula("q")


operator_via_or_not_and: Dict[str, Formula] = {
    BINARY_NOR: ~Placeholder.first & ~Placeholder.second,
    BINARY_NAND: ~Placeholder.first | ~Placeholder.second,
    BINARY_XOR: (~Placeholder.first & Placeholder.second)
    | (Placeholder.first & ~Placeholder.second),
    FALSE_OP: Placeholder.first & ~Placeholder.first,
    TRUE_OP: Placeholder.first | ~Placeholder.first,
}
logically_same_formula: Formula = ~operator_via_or_not_and[
    BINARY_XOR
]  # require being the same formula using logics
operator_via_or_not_and.update(
    {
        BINARY_IMPLY: ~Placeholder.first | logically_same_formula,
        BINARY_IFF: (~Placeholder.first | logically_same_formula)
        & (~Placeholder.second | logically_same_formula),
    }
)
transform_not_or_and_to_nand: Dict[str, Formula] = {
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
    NEGATE_SYM: Formula(BINARY_NAND, Placeholder.first, Placeholder.first),
}


def map_unallowed_to_allowed_ops(
    formula_operators: Set[str], allowed_ops: Set[str]
) -> Mapping[str, Formula]:
    """ """
    apply_or_not_and = apply_only_allowed_ops(allowed_ops)

    subtitution_map: Dict[str, Formula] = {
        op: apply_or_not_and[op]
        for op in formula_operators
        if op not in allowed_ops
    }

    return subtitution_map


def apply_only_allowed_ops(allowed_ops: Set[str]):
    if allowed_ops == {BINARY_OR, BINARY_AND, NEGATE_SYM}:
        return operator_via_or_not_and
    if allowed_ops == {BINARY_NAND}:
        transform_nand_to_not_or_and: Dict[str, Formula] = {
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
        return transform_nand_to_not_or_and


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
    allowed_ops: Set[str] = {BINARY_AND, BINARY_OR, NEGATE_SYM}
    subtitution_map: Mapping[str, Formula] = map_unallowed_to_allowed_ops(
        formula.operators(), allowed_ops
    )

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
    # allowed_ops: Set[str] = {BINARY_NAND}
    # subtitution_map: Mapping[str, Formula] = map_unallowed_to_allowed_ops(
    #     formula.operators(), allowed_ops
    # )

    # return formula.substitute_operators(subtitution_map)
    return formula.substitute_operators(
        operator_via_or_not_and
    ).substitute_operators(transform_not_or_and_to_nand)


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
