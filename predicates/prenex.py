# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.proofs import *
from predicates.prover import *
from predicates.syntax import *

#: Additional axioms of quantification for Predicate Logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(
        Formula.parse("((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))"),
        {"x", "R"},
    ),
    Schema(
        Formula.parse("((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))"),
        {"x", "R"},
    ),
    Schema(
        Formula.parse(
            "(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&"
            "(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&"
            "(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&"
            "(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&"
            "(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&"
            "(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&"
            "(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&"
            "(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&"
            "(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&"
            "(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&"
            "(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&"
            "(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&"
            "(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((R(x)->Q(x))&(Q(x)->R(x)))->"
            "((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))"
        ),
        {"x", "y", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((R(x)->Q(x))&(Q(x)->R(x)))->"
            "((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))"
        ),
        {"x", "y", "R", "Q"},
    ),
)


def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3a

    if is_quantifier(formula.root):
        return False
    if is_unary(formula.root):
        return is_quantifier_free(formula.first)
    if is_binary(formula.root):
        return is_quantifier_free(formula.first) and is_quantifier_free(
            formula.second
        )

    return True


def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3b

    #  Either quantifier-free or prefixed with quantifiers in-tandem,
    #  otherwise is not in the normal form
    if is_quantifier_free(formula):
        return True
    if is_quantifier(formula.root):
        return is_in_prenex_normal_form(formula.statement)

    return False


def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula(
        "&",
        Formula("->", formula1, formula2),
        Formula("->", formula2, formula1),
    )


def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both bound and
        free occurrences or is quantified by more than one quantifier, ``True``
        otherwise.

    Examples:
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ey[R(y)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(y=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ay[R(y)]|Ez[R(z)]))'))
        True
    """
    forbidden_variables = set(formula.free_variables())

    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(
                formula.first
            ) and has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.statement)
        else:
            assert is_equality(formula.root) or is_relation(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)


def _uniquely_rename_quantified_variables(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = _uniquely_rename_quantified_variables(
        ...     formula)
        >>> returned_formula
        ~(w=x|Az58[(Ez17[(z17=z58&Az4[z4=z17])]->Az32[z32=y])])
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert variable[0] != "z"
    # Task 11.5

    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)

    if is_quantifier_free(formula):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    elif is_unary(formula.root):
        refactored_argument, proof = _uniquely_rename_quantified_variables(
            formula.first
        )
        last_line = prover.add_proof(proof.conclusion, proof)

        new_formula = Formula(formula.root, refactored_argument)
        prover.add_tautological_implication(
            equivalence_of(formula, new_formula), {last_line}
        )

        return new_formula, prover.qed()

    elif is_binary(formula.root):
        refactored_first, proof = _uniquely_rename_quantified_variables(
            formula.first
        )
        first_arg_line = prover.add_proof(proof.conclusion, proof)

        refactored_second, proof = _uniquely_rename_quantified_variables(
            formula.second
        )
        second_arg_line = prover.add_proof(proof.conclusion, proof)

        new_formula = Formula(formula.root, refactored_first, refactored_second)

        prover.add_tautological_implication(
            equivalence_of(formula, new_formula),
            {first_arg_line, second_arg_line},
        )

        return new_formula, prover.qed()

    elif is_quantifier(formula.root):
        refactored_argument, proof = _uniquely_rename_quantified_variables(
            formula.statement
        )
        antecedent_line = prover.add_proof(proof.conclusion, proof)
        refactored_var = next(fresh_variable_name_generator)

        new_formula = Formula(
            formula.root,
            refactored_var,
            refactored_argument.substitute(
                {formula.variable: Term(refactored_var)}
            ),
        )
        conditional_formula = equivalence_of(formula, new_formula)

        conditional_line = prover.add_instantiated_assumption(
            Formula("->", proof.conclusion, conditional_formula),
            ADDITIONAL_QUANTIFICATION_AXIOMS[14 if formula.root == "A" else 15],
            {
                "x": formula.variable,
                "y": refactored_var,
                "R": formula.statement.substitute(
                    {formula.variable: Term("_")}
                ),
                "Q": refactored_argument.substitute(
                    {formula.variable: Term("_")}
                ),
            },
        )

        prover.add_mp(conditional_formula, antecedent_line, conditional_line)
        return new_formula, prover.qed()


def _pull_out_quantifications_across_negation(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = _pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6

    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)

    if not is_quantifier(formula.first.root):  # base case
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    else:
        quantifier = formula.first.root
        variable = formula.first.variable
        negated_arg = formula.first.statement

        axiom = 0 if quantifier == "A" else 1
        (
            pulled_inner_formula,
            pulled_inner_formula_proof,
        ) = _pull_out_quantifications_across_negation(
            Formula.parse(f"~{negated_arg}")
        )

        instantiation_map = {
            "x": variable,
            "R": negated_arg.substitute({variable: Term("_")}),
        }

        pull_equivalence = ADDITIONAL_QUANTIFICATION_AXIOMS[axiom].instantiate(
            instantiation_map
        )
        new_formula = pull_equivalence.first.second
        s1 = prover.add_instantiated_assumption(
            pull_equivalence,
            ADDITIONAL_QUANTIFICATION_AXIOMS[axiom],
            instantiation_map,
        )

        if is_quantifier(pulled_inner_formula.root):
            n2 = prover.add_proof(
                pulled_inner_formula_proof.conclusion,
                pulled_inner_formula_proof,
            )
            f1 = pulled_inner_formula_proof.conclusion.first.first
            f2 = pulled_inner_formula_proof.conclusion.first.second
            axiom = 14 if new_formula.root == "A" else 15
            instantiation_map = {
                "x": variable,
                "y": variable,
                "R": f1.substitute({variable: Term("_")}),
                "Q": f2.substitute({variable: Term("_")}),
            }
            pulled_inner_formula = ADDITIONAL_QUANTIFICATION_AXIOMS[
                axiom
            ].instantiate(instantiation_map)
            s3 = prover.add_instantiated_assumption(
                pulled_inner_formula,
                ADDITIONAL_QUANTIFICATION_AXIOMS[axiom],
                instantiation_map,
            )
            s4 = prover.add_mp(pulled_inner_formula.second, n2, s3)
            new_formula = pulled_inner_formula.second.first.second
            conclusion = equivalence_of(formula, new_formula)
            prover.add_tautological_implication(conclusion, {s1, s4})

        return new_formula, prover.qed()


def _pull_out_quantifications_from_left_across_binary_operator(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7a

    QUANTIFICATION_axioms_indices: Dict[str, int] = {"|": 6, "&": 2, "->": 10}

    return _pull_out_quantifiers_from_binary_formula(
        QUANTIFICATION_axioms_indices, formula, formula.first, formula.second
    )


def _pull_out_quantifications_from_right_across_binary_operator(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7b

    QUANTIFICATION_axioms_indices: Dict[str, int] = {"|": 8, "&": 4, "->": 12}

    return _pull_out_quantifiers_from_binary_formula(
        QUANTIFICATION_axioms_indices, formula, formula.second, formula.first
    )


def _pull_out_quantifiers_from_binary_formula(
    axiom_to_index: Dict[str, int],
    formula: Formula,
    rhs_formula: Formula,
    lhs_formula: Formula,
) -> Tuple[Formula, Proof]:

    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    op: str = formula.root

    if is_quantifier(rhs_formula.root):
        variable, quantifier, statement = (
            rhs_formula.variable,
            rhs_formula.root,
            rhs_formula.statement,
        )

        instantiation_map = {
            "Q": lhs_formula,
            "R": statement.substitute({variable: Term("_")}),
            "x": variable,
        }

        axiom_idx = axiom_to_index[op]
        if quantifier == "E":
            axiom_idx += 1
        equivalence: Optional[Formula] = ADDITIONAL_QUANTIFICATION_AXIOMS[
            axiom_idx
        ].instantiate(instantiation_map)

        step1 = prover.add_instantiated_assumption(
            equivalence,
            ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_idx],
            instantiation_map,
        )
        form = (
            Formula(op, rhs_formula.statement, lhs_formula)
            if formula.first == rhs_formula
            else Formula(op, lhs_formula, rhs_formula.statement)
        )
        form, pre = _pull_out_quantifiers_from_binary_formula(
            axiom_to_index, form, rhs_formula.statement, lhs_formula
        )
        new_formula: Formula = equivalence.first.second
        if is_quantifier(form.root):
            first1: Formula = pre.conclusion.first.first
            first2: Formula = pre.conclusion.first.second

            instantiation_map = {
                "Q": first2.substitute({variable: Term("_")}),
                "R": first1.substitute({variable: Term("_")}),
                "y": variable,
                "x": variable,
            }

            axiom_idx: int = 14 if new_formula.root == "A" else 15
            form = ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_idx].instantiate(
                instantiation_map
            )
            step2 = prover.add_instantiated_assumption(
                form,
                ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_idx],
                instantiation_map,
            )

            n = prover.add_proof(pre.conclusion, pre)
            step3 = prover.add_mp(form.second, n, step2)

            new_formula = form.second.first.second
            conclusion = equivalence_of(formula, new_formula)
            prover.add_tautological_implication(conclusion, {step3, step1})

        return new_formula, prover.qed()

    # Otherwise, not a quantification -> no-op
    prover.add_tautology(equivalence_of(formula, formula))
    return formula, prover.qed()


def _pull_out_quantifications_across_binary_operator(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8


def _to_prenex_normal_form_from_uniquely_named_variables(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = _to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9


def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = to_prenex_normal_form(formula)
        >>> returned_formula
        Ez58[Ez17[Az4[Ez32[~(w=x|((z17=z58&z4=z17)->z32=y))]]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert variable[0] != "z"
    # Task 11.10
