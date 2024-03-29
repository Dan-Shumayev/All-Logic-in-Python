# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/soundness.py

"""Programmatic proof of the soundness of Propositional Logic."""

from typing import Tuple

from propositions.proofs import *
from propositions.semantics import *
from propositions.syntax import *


def rule_nonsoundness_from_specialization_nonsoundness(
    general: InferenceRule, specialization: InferenceRule, model: Model
) -> Model:
    """Demonstrated the non-soundness of the given general inference rule given
    an example of the non-soundness of the given specialization of this rule.

    Parameters:
        general: inference rule to the soundness of which to find a
            counterexample.
        specialization: non-sound specialization of `general`.
        model: model in which `specialization` does not hold.

    Returns:
        A model in which `general` does not hold.
    """
    assert specialization.is_specialization_of(general)
    assert not evaluate_inference(specialization, model)
    # Task 4.9
    specialization_map: SpecializationMap = general.specialization_map(
        specialization
    )  # type: ignore

    return {
        var: evaluate(specialized_var, model)
        for var, specialized_var in specialization_map.items()
    }


def nonsound_rule_of_nonsound_proof(
    proof: Proof, model: Model
) -> Tuple[InferenceRule, Model]:
    """Finds a non-sound inference rule used by the given valid proof of a
    non-sound inference rule, and demonstrates the non-soundness of the former
    rule.

    Parameters:
        proof: valid proof of a non-sound inference rule.
        model: model in which the inference rule proved by the given proof does
            not hold.

    Returns:
        A pair of a non-sound inference rule used in the given proof and a model
        in which this rule does not hold.
    """
    assert proof.is_valid()
    assert not evaluate_inference(proof.statement, model)
    # Task 4.10
    for line_no, line in enumerate(proof.lines):
        line_rule: Optional[InferenceRule] = proof.rule_for_line(line_no)
        rule_used_by_line: Optional[InferenceRule] = line.rule

        if not line.is_assumption() and not evaluate_inference(
            line_rule, model  # type: ignore
        ):
            model_for_rule: Model = rule_nonsoundness_from_specialization_nonsoundness(
                rule_used_by_line, line_rule, model  # type: ignore
            )
            return (rule_used_by_line, model_for_rule)  # type: ignore
