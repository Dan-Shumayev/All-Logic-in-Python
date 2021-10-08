# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""

from propositions.axiomatic_systems import *
from propositions.proofs import *
from propositions.syntax import *


def prove_corollary(
    antecedent_proof: Proof, consequent: Formula, conditional: InferenceRule
) -> Proof:
    """Converts the given proof of a formula `antecedent` to a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    corollary_as_axiom: InferenceRule = InferenceRule(
        [],
        Formula(
            BINARY_IMPLY, antecedent_proof.statement.conclusion, consequent
        ),
    )
    assert corollary_as_axiom.is_specialization_of(conditional)
    # Task 5.3a

    statement: InferenceRule = InferenceRule(
        antecedent_proof.statement.assumptions, consequent
    )
    rules: FrozenSet[InferenceRule] = antecedent_proof.rules | {conditional, MP}

    antec_proof_lines_len: int = len(antecedent_proof.lines)

    return Proof(
        statement,
        rules,
        [
            *antecedent_proof.lines,
            Proof.Line(
                corollary_as_axiom.conclusion,
                conditional,
                [],
            ),
            Proof.Line(
                consequent,
                MP,
                [antec_proof_lines_len - 1, antec_proof_lines_len],
            ),
        ],
    )


def combine_proofs(
    antecedent1_proof: Proof,
    antecedent2_proof: Proof,
    consequent: Formula,
    double_conditional: InferenceRule,
) -> Proof:
    """Combines the given proofs of two formulas `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert (
        antecedent1_proof.statement.assumptions
        == antecedent2_proof.statement.assumptions
    )

    corollary_condition: Formula = antecedent1_proof.statement.conclusion
    corollary_conclusion: Formula = Formula(
        BINARY_IMPLY, antecedent2_proof.statement.conclusion, consequent
    )
    corollary_as_axiom: InferenceRule = InferenceRule(
        [],
        Formula(
            BINARY_IMPLY,
            corollary_condition,
            corollary_conclusion,
        ),
    )

    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert corollary_as_axiom.is_specialization_of(double_conditional)
    # Task 5.3b

    combined_proofs_statement: InferenceRule = InferenceRule(
        antecedent1_proof.statement.assumptions, consequent
    )
    combined_proofs_rules: AbstractSet[
        InferenceRule
    ] = antecedent1_proof.rules | {MP, double_conditional}

    antecedent1_proof_length: int = len(antecedent1_proof.lines)
    antecedent2_proof_length: int = len(antecedent2_proof.lines)
    combined_proofs_length: int = (
        antecedent1_proof_length + antecedent2_proof_length
    )

    return Proof(
        combined_proofs_statement,
        combined_proofs_rules,
        [
            *antecedent1_proof.lines,
            *increment_assumptions_in_lines(
                antecedent2_proof.lines, antecedent1_proof_length
            ),
            Proof.Line(
                corollary_as_axiom.conclusion,
                double_conditional,
                [],
            ),
            # Apply first Modus Ponens
            Proof.Line(
                corollary_as_axiom.conclusion.second,  # type: ignore
                MP,
                [
                    antecedent1_proof_length - 1,
                    combined_proofs_length,
                ],
            ),
            # Apply second Modus Ponens
            Proof.Line(
                consequent,
                MP,
                [
                    combined_proofs_length - 1,
                    combined_proofs_length + 1,
                ],
            ),
        ],
    )


def remove_assumption(proof: Proof) -> Proof:
    """Converts the given proof of some `conclusion` formula, the last
    assumption of which is an assumption `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4

    def find_formula_index(
        proof_lines: List[Proof.Line], formula: Formula
    ) -> int:
        for ix, line in enumerate(proof_lines):
            if line.formula == formula:
                return ix

    assumption_to_remove: Formula = proof.statement.assumptions[-1]

    statement_conclusion: Formula = Formula(
        BINARY_IMPLY, assumption_to_remove, proof.statement.conclusion
    )
    statement_to_prove: InferenceRule = InferenceRule(
        list(proof.statement.assumptions[:-1]), statement_conclusion
    )
    allowed_rules: AbstractSet[InferenceRule] = proof.rules | {MP, I0, I1, D}
    deduced_lines: List[Proof.Line] = list()

    for line_no, line in enumerate(proof.lines):
        if line.is_assumption():
            if line.formula == assumption_to_remove:  # Removed assumption
                deduced_lines.append(
                    Proof.Line(
                        Formula(
                            BINARY_IMPLY,
                            assumption_to_remove,
                            assumption_to_remove,
                        ),
                        I0,
                        [],
                    )
                )
            else:  # Another assumption in a set `A`
                required_conclusion: Formula = Formula(
                    BINARY_IMPLY,
                    assumption_to_remove,
                    line.formula,
                )
                deduced_lines.extend(
                    [
                        line,
                        Proof.Line(
                            Formula(
                                BINARY_IMPLY,
                                line.formula,
                                required_conclusion,
                            ),
                            I1,
                            [],
                        ),
                        Proof.Line(
                            required_conclusion,
                            MP,
                            [len(deduced_lines), len(deduced_lines) + 1],
                        ),
                    ]
                )
        elif not line.rule.assumptions:  # Justified by an assumptionless rule
            required_conclusion = Formula(
                BINARY_IMPLY,
                assumption_to_remove,
                line.formula,
            )

            deduced_lines.extend(
                [
                    line,
                    Proof.Line(
                        Formula(
                            BINARY_IMPLY,
                            line.formula,
                            required_conclusion,
                        ),
                        I1,
                        [],
                    ),
                    Proof.Line(
                        required_conclusion,
                        MP,
                        [len(deduced_lines), len(deduced_lines) + 1],
                    ),
                ]
            )
        else:  # Justified by two assumptions - MP
            specialization_map: SpecializationMap = {
                "p": assumption_to_remove,
                "q": proof.lines[line.assumptions[0]].formula,
                "r": line.formula,
            }
            apply_d_rule: Formula = D.conclusion.substitute_variables(
                specialization_map
            )
            deduced_lines.extend(
                [
                    Proof.Line(apply_d_rule, D, []),
                    Proof.Line(
                        apply_d_rule.second,
                        MP,
                        [
                            find_formula_index(
                                deduced_lines,
                                apply_d_rule.first,
                            ),
                            len(deduced_lines),
                        ],
                    ),
                    Proof.Line(
                        apply_d_rule.second.second,
                        MP,
                        [
                            find_formula_index(
                                deduced_lines, apply_d_rule.second.first
                            ),
                            len(deduced_lines) + 1,
                        ],
                    ),
                ]
            )

    conclusion_line: Proof.Line = deduced_lines.pop()
    deduced_lines.append(
        Proof.Line(
            statement_conclusion,
            conclusion_line.rule,
            conclusion_line.assumptions,
        )
    )
    return Proof(statement_to_prove, allowed_rules, deduced_lines)


def prove_from_opposites(
    proof_of_affirmation: Proof, proof_of_negation: Proof, conclusion: Formula
) -> Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert (
        proof_of_affirmation.statement.assumptions
        == proof_of_negation.statement.assumptions
    )
    assert (
        Formula("~", proof_of_affirmation.statement.conclusion)
        == proof_of_negation.statement.conclusion
    )
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6


def prove_by_way_of_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, to a proof of `formula` from the
    same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse("~(p->p)")
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == "~"
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
