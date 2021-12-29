# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in Predicate Logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable name that is free in this assumption.
        print_as_proof_forms: flag specifying whether the proof of
            ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.1

    prover = Prover(
        {a for a in proof.assumptions if a.formula != assumption},
        print_as_proof_forms)
    fi = assumption
    line_mapper = dict()

    for i in range(len(proof.lines)):
        line = proof.lines[i]

        if isinstance(line, Proof.TautologyLine) or line.formula == fi:
            last_step = prover.add_tautology(f'({fi}->{line.formula})')

        elif isinstance(line, Proof.AssumptionLine):
            a = line.formula
            step1 = prover.add_instantiated_assumption(a, line.assumption,
                                                       line.instantiation_map)
            step2 = prover.add_tautology(f'({a}->({fi}->{a}))')
            last_step = prover.add_mp(f'({fi}->{a})', step1, step2)

        elif isinstance(line, Proof.MPLine):
            a, b = proof.lines[line.antecedent_line_number].formula, \
                   line.formula
            step1 = prover.add_tautology(
                f'(({fi}->({a}->{b}))->(({fi}->{a})->({fi}->{b}))')
            step2 = prover.add_mp(
                f'(({fi}->{a})->({fi}->{b}))',
                line_mapper[line.conditional_line_number], step1)
            last_step = prover.add_mp(
                f'({fi}->{b})', line_mapper[line.antecedent_line_number], step2)

        else:  # isinstance(line, Proof.UGLine)
            a, x = proof.lines[line.nonquantified_line_number].formula, line.formula.variable
            step1 = prover.add_ug(
                f'A{x}[({fi}->{a})]', line_mapper[line.nonquantified_line_number])
            us_map = {'Q': fi,
                      'R': a.substitute({x: Term.parse('_')}, set()),
                      'x': x}
            ins = Prover.US.instantiate(us_map)
            step2 = prover.add_instantiated_assumption(
                ins, Prover.US, us_map)  # maybe try explicitly instantiating
            last_step = prover.add_mp(f'({fi}->A{x}[{a}])', step1, step2)

        line_mapper[i] = last_step

    return prover.qed()

    # prover = Prover({a for a in proof.assumptions if a.formula != assumption}, True) # print_as_proof_forms)
    # phi = assumption
    # line_in_new_proof = dict()
    #
    # for i, line in enumerate(proof.lines):
    #     if isinstance(line, Proof.TautologyLine) or line.formula == phi:
    #         line_in_new_proof[i] = prover.add_tautology(f'({phi}->{line.formula})')
    #
    #     elif isinstance(line, Proof.AssumptionLine):
    #         alpha = line.formula
    #         step1 = prover.add_instantiated_assumption(alpha, line.assumption, line.instantiation_map)
    #         step2 = prover.add_tautology(f'({alpha}->({phi}->{alpha}))')
    #         line_in_new_proof[i] = prover.add_mp(f'({phi}->{alpha})', step1, step2)
    #
    #     elif isinstance(line, Proof.MPLine):
    #         alpha = proof.lines[line.antecedent_line_number].formula
    #         beta = line.formula
    #         step1 = prover.add_tautology(f'(({phi}->({alpha}->{beta}))->(({phi}->{alpha})->({phi}->{beta}))')
    #         step2 = prover.add_mp(f'(({phi}->{alpha})->({phi}->{beta}))', line_in_new_proof[line.conditional_line_number], step1)
    #         line_in_new_proof[i] = prover.add_mp(f'({phi}->{beta})', line_in_new_proof[line.antecedent_line_number], step2)
    #
    #     elif isinstance(line, Proof.UGLine):
    #         alpha: Formula = proof.lines[line.nonquantified_line_number].formula
    #         x = line.formula.variable
    #         step1 = prover.add_ug(f'A{x}[({phi}->{alpha})]', line_in_new_proof[line.nonquantified_line_number])
    #         us_map = {'Q': phi, 'R': alpha, 'x': x}
    #         step2 = prover.add_instantiated_assumption(Prover.US.instantiate(us_map), Prover.US, us_map)
    #         line_in_new_proof[i] = prover.add_mp(f'({phi}->A{x}[{alpha}])', step1, step2)
    #
    # return prover.qed()



def prove_by_way_of_contradiction(proof: Proof, assumption: Formula) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable name that is free in this assumption.

    Returns:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.2
