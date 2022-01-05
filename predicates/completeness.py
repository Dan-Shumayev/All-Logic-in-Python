# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: predicates/completeness.py

"""Building blocks for proving the Completeness Theorem for Predicate Logic."""

import enum
from functools import reduce as ft_reduce
from itertools import product as it_product
from typing import AbstractSet, Container, Set, Union

from logic_utils import fresh_constant_name_generator

from predicates.deduction import *
from predicates.prenex import *
from predicates.proofs import *
from predicates.prover import *
from predicates.semantics import *
from predicates.syntax import *


def get_constants(formulas: AbstractSet[Formula]) -> Set[str]:
    """Finds all constant names in the given formulas.

    Parameters:
        formulas: formulas to find all constant names in.

    Returns:
        A set of all constant names used in one or more of the given formulas.
    """
    constants = set()
    for formula in formulas:
        constants.update(formula.constants())
    return constants


def is_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if the given set of sentences is primitively, universally, and
        existentially closed; ``False`` otherwise.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence)
            and len(sentence.free_variables()) == 0
        )
    return (
        is_primitively_closed(sentences)
        and is_universally_closed(sentences)
        and is_existentially_closed(sentences)
    )


def is_primitively_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    primitively closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every n-ary relation name from the given sentences, and
        for every n (not necessarily distinct) constant names from the given
        sentences, either the invocation of this relation name over these
        constant names (in order), or the negation of this invocation (or both),
        is one of the given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence)
            and len(sentence.free_variables()) == 0
        )
    # Task 12.1a

    return all(
        all(
            Formula(relation, [Term(a) for a in arguments]) in sentences
            or Formula("~", Formula(relation, [Term(a) for a in arguments]))
            in sentences
            for arguments in it_product(get_constants(sentences), repeat=arity)
        )
        for relation, arity in get_relations(sentences)
    )


def get_relations(sentences: AbstractSet[Formula]) -> Set[Tuple[str, int]]:
    return set(
        ft_reduce(
            lambda rel1, rel2: rel1 | rel2,
            (sentence.relations() for sentence in sentences),
        )
    )


def is_universally_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    universally closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every universally quantified sentence from the given set
        of sentences, and for every constant name from these sentences, the
        statement quantified by this sentence, with every free occurrence of the
        universal quantification variable name replaced with this constant name,
        is also in the given set; ``False`` otherwise.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence)
            and len(sentence.free_variables()) == 0
        )
    # Task 12.1b
    return all(
        all(
            sentence.statement.substitute({sentence.variable: Term(c)})
            in sentences
            for c in get_constants(sentences)
        )
        for sentence in sentences
        if sentence.root == "A"
    )


def is_existentially_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    existentially closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every existentially quantified sentence from the given
        set of sentences there exists a constant name such that the statement
        quantified by this sentence, with every free occurrence of the
        existential quantification variable name replaced with this constant
        name, is also in the given set; ``False`` otherwise.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence)
            and len(sentence.free_variables()) == 0
        )
    # Task 12.1c
    return all(
        any(
            sentence.statement.substitute({sentence.variable: Term(c)})
            in sentences
            for c in get_constants(sentences)
        )
        for sentence in sentences
        if sentence.root == "E"
    )


def find_unsatisfied_quantifier_free_sentence(
    sentences: Container[Formula], model: Model[str], unsatisfied: Formula
) -> Formula:
    """
    Given a universally and existentially closed set of prenex-normal-form
    sentences, given a model whose universe is the set of all constant names
    from the given sentences, and given a sentence from the given set that the
    given model does not satisfy, finds a quantifier-free sentence from the
    given set that the given model does not satisfy.

    Parameters:
        sentences: universally and existentially closed set of
            prenex-normal-form sentences, which is only to be accessed using
            containment queries, i.e., using the ``in`` operator as in:

            >>> if sentence in sentences:
            ...     print('contained!')

        model: model for all element names from the given sentences, whose
            universe is `get_constants`\ ``(``\ `sentences`\ ``)``.
        unsatisfied: sentence (which possibly contains quantifiers) from the
            given sentences that is not satisfied by the given model.

    Returns:
        A quantifier-free sentence from the given set of sentences that is not
        satisfied by the given model.
    """
    # We assume that every formula in sentences is in prenex normal form and has
    # no free variable names, that sentences is universally and existentially
    # closed, and that the set of constant names that appear somewhere in
    # sentences is model.universe; but we cannot assert these since we cannot
    # iterate over sentences.
    for constant in model.universe:
        assert is_constant(constant)
    assert is_in_prenex_normal_form(unsatisfied)
    assert len(unsatisfied.free_variables()) == 0
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)
    # Task 12.2
    if not is_quantifier(unsatisfied.root):
        return unsatisfied

    variable: str = unsatisfied.variable
    statement: Formula = unsatisfied.statement

    for const in model.universe:
        statement_instantiated: Formula = statement.substitute(
            {variable: Term(const)}
        )
        if (
            not model.evaluate_formula(statement_instantiated)
            and statement_instantiated in sentences
        ):
            return find_unsatisfied_quantifier_free_sentence(
                sentences, model, statement_instantiated
            )


def get_primitives(quantifier_free: Formula) -> Set[Formula]:
    """Finds all primitive subformulas of the given quantifier-free formula.

    Parameters:
        quantifier_free: quantifier-free formula that contains no function names
            and no equalities, whose subformulas are to be searched.

    Returns:
        The primitive subformulas (i.e., relation invocations) of which the
        given quantifier-free formula is composed using logical operators.

    Examples:
        The primitive subformulas of ``'(R(c1,d)|~(Q(c1)->~R(c2,a)))'`` are
        ``'R(c1,d)'``, ``'Q(c1)'``, and ``'R(c2,a)'``.
    """
    assert is_quantifier_free(quantifier_free)
    assert len(quantifier_free.functions()) == 0
    assert "=" not in str(quantifier_free)
    # Task 12.3a

    return quantifier_free.propositional_skeleton()[1].values()


def model_or_inconsistency(
    sentences: AbstractSet[Formula],
) -> Union[Model[str], Proof]:
    """Either finds a model in which the given closed set of prenex-normal-form
    sentences holds, or proves a contradiction from these sentences.

    Parameters:
        sentences: closed set of prenex-normal-form sentences that contain no
            function names and no equalities, to either find a model of, or
            prove a contradiction from.

    Returns:
        A model in which all of the given sentences hold if such exists,
        otherwise a valid proof of a contradiction from the given formulas via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_closed(sentences)
    for relation in sentences:
        assert len(relation.functions()) == 0
        assert "=" not in str(relation)
    # Task 12.3b

    constants: Set[str] = get_constants(sentences)
    relations: Set[Tuple[str, int]] = get_relations(sentences)
    constant_interpretations: Dict[str, str] = {c: c for c in constants}

    relation_interpretations: Dict[str, Set[int]] = {
        r: set() for r, _ in relations
    }

    for sentence in sentences:
        if is_relation(sentence.root):
            args: Tuple[str] = tuple(arg.root for arg in sentence.arguments)
            relation_interpretations[sentence.root].add(args)

    model = Model(
        constants, constant_interpretations, relation_interpretations, {}
    )

    unsatisfied: Optional[Formula] = None
    for sentence in sentences:
        if not model.evaluate_formula(sentence):
            unsatisfied = sentence

    if unsatisfied:
        unsatisfied_quantifier_free: Formula = (
            find_unsatisfied_quantifier_free_sentence(
                sentences, model, unsatisfied
            )
        )

        primitives: Set[Formula] = get_primitives(unsatisfied_quantifier_free)

        contradicting_sentences: Set[Formula] = {unsatisfied_quantifier_free}

        for p in primitives:
            if p in sentences:
                contradicting_sentences.add(p)
            else:
                not_p = Formula("~", p)
                assert not_p in sentences
                contradicting_sentences.add(not_p)

        prover = Prover(contradicting_sentences)
        for assumption in contradicting_sentences:
            prover.add_assumption(assumption)

        contradiction = Formula.parse("(z=z&~z=z)")

        prover.add_tautological_implication(
            contradiction, set(range(len(contradicting_sentences)))
        )

        return prover.qed()

    return model


def combine_contradictions(
    proof_from_affirmation: Proof, proof_from_negation: Proof
) -> Proof:
    """Combines the given two proofs of contradictions, both from the same
    assumptions/axioms except that the latter has an extra assumption that is
    the negation of an extra assumption that the former has, into a single proof
    of a contradiction from only the common assumptions/axioms.

    Parameters:
        proof_from_affirmation: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        proof_from_negation: valid proof of a contradiction from the same
            assumptions/axioms of `proof_from_affirmation`, but with one
            simple assumption (i.e., without any templates) `assumption`
            replaced with its negation ``'~``\ `assumption`\ ``'``.

    Returns:
        A valid proof of a contradiction from only the assumptions/axioms common
        to the given proofs (i.e., without `assumption` or its negation).
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions
    )
    assert (
        len(common_assumptions) == len(proof_from_affirmation.assumptions) - 1
    )
    assert len(common_assumptions) == len(proof_from_negation.assumptions) - 1
    affirmed_assumption = list(
        proof_from_affirmation.assumptions - common_assumptions
    )[0]
    negated_assumption = list(
        proof_from_negation.assumptions - common_assumptions
    )[0]
    assert len(affirmed_assumption.templates) == 0
    assert len(negated_assumption.templates) == 0
    assert negated_assumption.formula == Formula(
        "~", affirmed_assumption.formula
    )
    assert proof_from_affirmation.assumptions.issuperset(Prover.AXIOMS)
    assert proof_from_negation.assumptions.issuperset(Prover.AXIOMS)
    for assumption in common_assumptions.union(
        {affirmed_assumption, negated_assumption}
    ):
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.4

    prover = Prover(common_assumptions)

    p1: Proof = remove_assumption(
        proof_from_affirmation, affirmed_assumption.formula
    )
    p2: Proof = remove_assumption(
        proof_from_negation, negated_assumption.formula
    )

    conclusion1_line: int = prover.add_proof(p1.conclusion, p1)
    conclusion2_line: int = prover.add_proof(p2.conclusion, p2)
    conclusion3_line: int = prover.add_tautological_implication(
        f"({p1.conclusion}&{p2.conclusion})",
        {conclusion1_line, conclusion2_line},
    )

    prover.add_tautological_implication("(z=z&~z=z)", {conclusion3_line})

    return prover.qed()


def eliminate_universal_instantiation_assumption(
    proof: Proof, universal: Formula, constant: str
) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `universal` and `instantiation`, where the latter is the universal
    instantiation of the former with the constant name `constant`, to a proof
    of a contradiction from the same assumptions without `instantiation`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        universal: assumption of the given proof that is universally quantified.
        constant: constant name such that the formula `instantiation` obtained
            from the statement quantified by `universal` by replacing all free
            occurrences of the universal quantification variable name by the
            given constant name, is an assumption of the given proof.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        given proof except `instantiation`.
    """
    assert proof.is_valid()
    assert Schema(universal) in proof.assumptions
    assert universal.root == "A"
    assert is_constant(constant)
    assert (
        Schema(
            universal.statement.substitute({universal.variable: Term(constant)})
        )
        in proof.assumptions
    )
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.5

    substituted_removed_assum = universal.statement.substitute(
        {universal.variable: Term(constant)}
    )
    prover = Prover(proof.assumptions - {Schema(substituted_removed_assum)})
    removed_assum: Proof = remove_assumption(
        proof,
        substituted_removed_assum,
    )
    prover.add_proof(removed_assum.conclusion, removed_assum)

    line = prover.add_instantiated_assumption(
        f"({universal}->{substituted_removed_assum})",
        Prover.UI,
        {
            "x": universal.variable,
            "c": constant,
            "R": universal.statement.substitute(
                {universal.variable: Term("_")}
            ),
        },
    )
    line2 = prover.add_assumption(universal)

    line3 = prover.add_mp(
        prover._lines[line].formula.second,
        line2,
        line,
    )

    prover.add_mp(
        prover._lines[len(removed_assum.lines) - 1].formula.second,
        line3,
        len(removed_assum.lines) - 1,
    )

    return prover.qed()


def universal_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with all universal instantiations of each
    universally quantified sentence from these sentences, with respect to all
    constant names from these sentences.

    Parameters:
        sentences: prenex-normal-form sentences to augment with their universal
            instantiations.

    Returns:
        A set of all of the given sentences, and in addition any formula that
        can be obtained from the statement quantified by any universally
        quantified sentence from the given sentences by replacing all
        occurrences of the quantification variable name with some constant name
        from the given sentences.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence)
            and len(sentence.free_variables()) == 0
        )
    # Task 12.6

    constants = get_constants(sentences)
    augmented_sentences = list(sentences)

    for sentence in sentences:
        if sentence.root == "A":
            statement = sentence.statement
            variable = sentence.variable
            augmented_sentences.extend(
                [
                    statement.substitute({variable: Term(constant)})
                    for constant in constants
                ]
            )

    return set(augmented_sentences)


def replace_constant(
    proof: Proof, constant: str, variable: str = "zz"
) -> Proof:
    """Replaces all occurrences of the given constant name in the given proof
    with the given variable name.

    Parameters:
        proof: valid proof in which to replace.
        constant: constant name that does not appear as a template constant name
            in any of the assumptions of the given proof.
        variable: variable name that does not appear anywhere in the given proof
            or in its assumptions.

    Returns:
        A valid proof where every occurrence of the given constant name in the
        given proof and in its assumptions is replaced with the given variable
        name.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert is_variable(variable)
    for assumption in proof.assumptions:
        assert constant not in assumption.templates
        assert variable not in assumption.formula.variables()
    for line in proof.lines:
        assert variable not in line.formula.variables()
    # Task 12.7a

    new_const_to_new_var: Dict[str, Term] = {constant: Term(variable)}

    prover = Prover(
        {
            Schema(
                assum.formula.substitute(new_const_to_new_var), assum.templates
            )
            for assum in proof.assumptions
        }
    )

    for line in proof.lines:
        line_formula_substituted = line.formula.substitute(new_const_to_new_var)

        if isinstance(line, Proof.TautologyLine):
            prover.add_tautology(line_formula_substituted)
        elif isinstance(line, Proof.MPLine):
            prover.add_mp(
                line_formula_substituted,
                line.antecedent_line_number,
                line.conditional_line_number,
            )
        elif isinstance(line, Proof.UGLine):
            prover.add_ug(
                line_formula_substituted, line.nonquantified_line_number
            )
        else:
            assert isinstance(line, Proof.AssumptionLine)
            instantiation_map: InstantiationMap = dict()

            sub_ass = Schema(
                line.assumption.formula.substitute(new_const_to_new_var),
                line.assumption.templates,
            )

            for k, v in line.instantiation_map.items():
                if type(v) is str:
                    if v != constant:
                        instantiation_map[k] = v
                    else:
                        instantiation_map[k] = variable
                else:
                    instantiation_map[k] = v.substitute(new_const_to_new_var)

            prover.add_instantiated_assumption(
                line_formula_substituted, sub_ass, instantiation_map
            )

    return prover.qed()


def eliminate_existential_witness_assumption(
    proof: Proof, existential: Formula, constant: str
) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `existential` and `witness`, where the latter is the existential
    witness of the former with the witnessing constant name `constant`, to a
    proof of a contradiction from the same assumptions without `witness`.

    Parameters:
        proof: valid proof, which does not contain the variable name ``'zz'`` in
            its lines or assumptions, of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        existential: assumption of the given proof that is existentially
            quantified.
        constant: constant name such that the formula `witness` obtained from
            from the statement quantified by `existential` by replacing all free
            occurrences of the existential quantification variable name by the
            given constant name, is an assumption of the given proof, and such
            that this constant name does not appear in any assumption of the
            given proof except `witness`.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        given proof except `witness`.
    """
    assert proof.is_valid()
    assert Schema(existential) in proof.assumptions
    assert existential.root == "E"
    assert is_constant(constant)
    witness = existential.statement.substitute(
        {existential.variable: Term(constant)}
    )
    assert Schema(witness) in proof.assumptions
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
        assert "zz" not in assumption.formula.variables()
    for assumption in proof.assumptions - {Schema(witness)}:
        assert constant not in assumption.formula.constants()
    for line in proof.lines:
        assert "zz" not in line.formula.variables()
    # Task 12.7b

    prover = Prover(proof.assumptions - {Schema(witness)})

    witness_z: Formula = witness.substitute({constant: Term("zz")})
    proof_of_witness_negation: Proof = prove_by_way_of_contradiction(
        replace_constant(proof, constant), witness_z
    )

    added_line1: int = prover.add_proof(
        proof_of_witness_negation.conclusion, proof_of_witness_negation
    )

    phi: Formula = existential.statement

    witness_and_its_negation_contrad = Formula(
        "&", witness_z, Formula("~", witness_z)
    )
    phi_implies_contrad = Formula("->", phi, witness_and_its_negation_contrad)

    added_line2 = prover.add_free_instantiation(
        Formula("~", phi), added_line1, {"zz": existential.variable}
    )

    added_line3 = prover.add_assumption(existential)
    added_line4 = prover.add_tautological_implication(
        phi_implies_contrad, {added_line2}
    )

    prover.add_existential_derivation(
        witness_and_its_negation_contrad, added_line3, added_line4
    )

    return prover.qed()


def existential_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with an existential witness that uses a new
    constant name, for each existentially quantified sentence from these
    sentences for which an existential witness is missing.

    Parameters:
        sentences: prenex-normal-form sentences to augment with any missing
            existential witnesses.

    Returns:
        A set of all of the given sentences, and in addition for every
        existentially quantified sentence from the given sentences, a formula
        obtained from the statement quantified by that sentence by replacing all
        occurrences of the quantification variable name with a new constant name
        obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_constant_name_generator`\ ``)``.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence)
            and len(sentence.free_variables()) == 0
        )
    # Task 12.8

    constants: Set[str] = get_constants(sentences)
    augmented_sentences: Set[Formula] = set(sentences)

    for sentence in sentences:
        if sentence.root == "E":
            existential_var: str = sentence.variable
            existential_statement: Formula = sentence.statement

            if all(
                existential_statement.substitute(
                    {existential_var: Term(constant)}
                )
                not in sentences
                for constant in constants
            ):
                generated_witness: Formula = existential_statement.substitute(
                    {existential_var: Term(next(fresh_constant_name_generator))}
                )
                augmented_sentences.add(generated_witness)

    return augmented_sentences
