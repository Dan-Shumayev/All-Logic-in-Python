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
    """Converts a proof of some `conclusion` formula, the last assumption of
    which is an assumption `assumption`, into a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.
    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.
    Return:
        A valid proof of ``'(``\ `assumptions`\ ``->``\ `conclusion`\ ``)'``
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

    # TODO - change it!

    phi: Formula = proof.statement.assumptions[-1]
    a_assums = proof.statement.assumptions[:-1]
    a_assums_set = set(a_assums)  # for faster checking
    result = Formula("->", phi, proof.statement.conclusion)
    new_statement = InferenceRule(a_assums, result)
    rules = proof.rules | {MP, I0, I1, D}
    lines = []
    # maps index i foreach xsi_i in given proof,
    # to index of (phi -> xsi_i) in new proof
    old_to_new: Dict[int, int] = {}
    for i, xsi in enumerate(proof.lines):
        phi_to_xsi = Formula("->", phi, xsi.formula)
        if xsi.is_assumption() and xsi.formula in a_assums_set:

            xsi_index = len(lines)
            lines.append(Proof.Line(xsi.formula))

            phi_to_xsi = Formula("->", phi, xsi.formula)
            xsi_to_phi_to_xsi = Formula("->", xsi.formula, phi_to_xsi)

            i1_term_index = len(lines)
            lines.append(Proof.Line(xsi_to_phi_to_xsi, I1, []))

            lines.append(Proof.Line(phi_to_xsi, MP, [xsi_index, i1_term_index]))
            old_to_new[i] = len(lines) - 1

        elif xsi.is_assumption() and xsi.formula == phi:
            lines.append(Proof.Line(phi_to_xsi, I0, []))
            old_to_new[i] = len(lines) - 1
        elif xsi.rule == MP:
            assert not xsi.is_assumption()
            j, k = xsi.assumptions[0], xsi.assumptions[1]
            xsi_j, xsi_j_to_xsi_k = (
                proof.lines[j].formula,
                proof.lines[k].formula,
            )
            xsi_k = xsi_j_to_xsi_k.second

            j_new, k_new = old_to_new[j], old_to_new[k]

            # specializing D, with p=phi, q=xsi_j, r=xsi_k
            # eventual result will be phi -> xsi_k

            # first, lets define a bunch of terms that we'll need
            phi_to_xsi_j = Formula("->", phi, xsi_j)
            phi_to_xsi_k = Formula("->", phi, xsi_k)
            d_left_term = Formula("->", phi, xsi_j_to_xsi_k)
            d_right_term = Formula("->", phi_to_xsi_j, phi_to_xsi_k)
            d_term = Formula("->", d_left_term, d_right_term)

            phi_to_xsi_j_to_xsi_k = Formula(
                "->", phi, Formula("->", xsi_j, xsi_k)
            )

            # sanity-checks
            assert phi_to_xsi_j == lines[j_new].formula
            assert phi_to_xsi_j_to_xsi_k == lines[k_new].formula
            assert d_left_term == phi_to_xsi_j_to_xsi_k

            d_index = len(lines)
            lines.append(Proof.Line(d_term, D, []))

            # now apply MP twice to extract the phi -> xsi_k term in D
            # first MP applies 'phi -> (xsi_j -> xsi_k)' onto D, corresponding
            # to its left term, extracting the right term, which requires
            # phi_to_xsi_j
            extracted_right_term_index = len(lines)
            lines.append(Proof.Line(d_right_term, MP, [k_new, d_index]))

            lines.append(
                Proof.Line(
                    phi_to_xsi_k, MP, [j_new, extracted_right_term_index]
                )
            )
            old_to_new[i] = len(lines) - 1

        else:
            assert not xsi.is_assumption()
            assert len(xsi.assumptions) == 0
            # we can use I1 (q -> (p -> q)) with q=xsi and p=phi
            # then apply xsi(from original line) onto that formula via MP,
            # getting (phi -> xsi)
            xsi_index = len(lines)
            lines.append(xsi)

            i1_index = len(lines)
            lines.append(
                Proof.Line(Formula("->", xsi.formula, phi_to_xsi), I1, [])
            )

            lines.append(Proof.Line(phi_to_xsi, MP, [xsi_index, i1_index]))
            old_to_new[i] = len(lines) - 1

    removed = Proof(new_statement, rules, lines)
    return removed


# def remove_assumption(proof: Proof) -> Proof:
#     """Converts the given proof of some `conclusion` formula, the last
#     assumption of which is an assumption `assumption`, to a proof of
#     ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
#     except `assumption`.

#     Parameters:
#         proof: valid proof to convert, with at least one assumption, via some
#             set of inference rules all of which have no assumptions except
#             perhaps `~propositions.axiomatic_systems.MP`.

#     Returns:
#         A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
#         from the same assumptions as the given proof except the last one, via
#         the same inference rules as the given proof and in addition
#         `~propositions.axiomatic_systems.MP`,
#         `~propositions.axiomatic_systems.I0`,
#         `~propositions.axiomatic_systems.I1`, and
#         `~propositions.axiomatic_systems.D`.
#     """
#     assert proof.is_valid()
#     assert len(proof.statement.assumptions) > 0
#     for rule in proof.rules:
#         assert rule == MP or len(rule.assumptions) == 0
#     # Task 5.4
#     # TODO - refactor
#     def find_formula_index(
#         proof_lines: List[Proof.Line], formula: Formula
#     ) -> int:
#         for ix, line in enumerate(proof_lines):
#             if line.formula == formula:
#                 return ix

#     assumption_to_remove: Formula = proof.statement.assumptions[-1]

#     statement_conclusion: Formula = Formula(
#         BINARY_IMPLY, assumption_to_remove, proof.statement.conclusion
#     )
#     statement_to_prove: InferenceRule = InferenceRule(
#         list(proof.statement.assumptions[:-1]), statement_conclusion
#     )
#     allowed_rules: AbstractSet[InferenceRule] = proof.rules | {MP, I0, I1, D}
#     deduced_lines: List[Proof.Line] = list()

#     for line_no, line in enumerate(proof.lines):
#         if line.is_assumption():
#             if line.formula == assumption_to_remove:  # Removed assumption
#                 deduced_lines.append(
#                     Proof.Line(
#                         Formula(
#                             BINARY_IMPLY,
#                             assumption_to_remove,
#                             assumption_to_remove,
#                         ),
#                         I0,
#                         [],
#                     )
#                 )
#             else:  # Another assumption in a set `A`
#                 required_conclusion: Formula = Formula(
#                     BINARY_IMPLY,
#                     assumption_to_remove,
#                     line.formula,
#                 )
#                 deduced_lines.extend(
#                     [
#                         line,
#                         Proof.Line(
#                             Formula(
#                                 BINARY_IMPLY,
#                                 line.formula,
#                                 required_conclusion,
#                             ),
#                             I1,
#                             [],
#                         ),
#                         Proof.Line(
#                             required_conclusion,
#                             MP,
#                             [len(deduced_lines), len(deduced_lines) + 1],
#                         ),
#                     ]
#                 )
#         elif not line.rule.assumptions:  # Justified by an assumptionless rule
#             required_conclusion = Formula(
#                 BINARY_IMPLY,
#                 assumption_to_remove,
#                 line.formula,
#             )

#             deduced_lines.extend(
#                 [
#                     line,
#                     Proof.Line(
#                         Formula(
#                             BINARY_IMPLY,
#                             line.formula,
#                             required_conclusion,
#                         ),
#                         I1,
#                         [],
#                     ),
#                     Proof.Line(
#                         required_conclusion,
#                         MP,
#                         [len(deduced_lines), len(deduced_lines) + 1],
#                     ),
#                 ]
#             )
#         else:  # Justified by two assumptions - MP
#             specialization_map: SpecializationMap = {
#                 "p": assumption_to_remove,
#                 "q": proof.lines[line.assumptions[0]].formula,
#                 "r": line.formula,
#             }
#             apply_d_rule: Formula = D.conclusion.substitute_variables(
#                 specialization_map
#             )
#             deduced_lines.extend(
#                 [
#                     Proof.Line(apply_d_rule, D, []),
#                     Proof.Line(
#                         apply_d_rule.second,
#                         MP,
#                         [
#                             find_formula_index(
#                                 deduced_lines,
#                                 apply_d_rule.first,
#                             ),
#                             len(deduced_lines),
#                         ],
#                     ),
#                     Proof.Line(
#                         apply_d_rule.second.second,
#                         MP,
#                         [
#                             find_formula_index(
#                                 deduced_lines, apply_d_rule.second.first
#                             ),
#                             len(deduced_lines) + 1,
#                         ],
#                     ),
#                 ]
#             )

#     conclusion_line: Proof.Line = deduced_lines.pop()
#     deduced_lines.append(
#         Proof.Line(
#             statement_conclusion,
#             conclusion_line.rule,
#             conclusion_line.assumptions,
#         )
#     )
#     return Proof(statement_to_prove, allowed_rules, deduced_lines)


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

    statement: InferenceRule = InferenceRule(
        proof_of_affirmation.statement.assumptions, conclusion
    )
    rules: AbstractSet[InferenceRule] = proof_of_affirmation.rules | {MP, I2}
    lines: Tuple[Proof.Line, ...] = combine_proofs(
        proof_of_negation,
        proof_of_affirmation,
        conclusion,
        I2,
    ).lines

    return Proof(statement, rules, lines)


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

    statement: InferenceRule = InferenceRule(
        proof.statement.assumptions[:-1], proof.statement.assumptions[-1].first
    )
    rules: AbstractSet[InferenceRule] = {MP, I0, I1, D, N} | proof.rules

    proof_without_last_assum: Proof = remove_assumption(proof)
    proof_length = len(proof_without_last_assum.lines)

    converse_main_conclusion: Formula = proof.statement.conclusion.first  # type: ignore
    converse_required_conclusion: Formula = (
        proof.statement.assumptions[  # type:ignore
            -1
        ].first
    )

    specialized_conclusion_by_n: Formula = Formula(
        BINARY_IMPLY,
        converse_main_conclusion,
        converse_required_conclusion,
    )

    return Proof(
        statement,
        rules,
        list(proof_without_last_assum.lines)
        + [
            Proof.Line(
                Formula(
                    BINARY_IMPLY,
                    proof_without_last_assum.lines[-1].formula,
                    specialized_conclusion_by_n,
                ),
                N,
                [],
            ),
            Proof.Line(
                specialized_conclusion_by_n,
                MP,
                [
                    proof_length - 1,
                    proof_length,
                ],
            ),
            Proof.Line(converse_main_conclusion, I0, []),
            Proof.Line(
                converse_required_conclusion,
                MP,
                [
                    proof_length + 2,
                    proof_length + 1,
                ],
            ),
        ],
    )
