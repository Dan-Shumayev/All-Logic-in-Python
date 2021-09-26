# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/proofs.py

"""Proofs by deduction in Propositional Logic."""

from __future__ import annotations

from typing import (
    AbstractSet,
    FrozenSet,
    Generator,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from logic_utils import frozen, memoized_parameterless_method

from propositions.syntax import *

#: A mapping from variable names to formulas.
SpecializationMap = Mapping[str, Formula]


@frozen
class InferenceRule:
    """An immutable inference rule in Propositional Logic, comprised of zero
    or more assumed propositional formulas, and a conclusion propositional
    formula.

    Attributes:
        assumptions (`~typing.Tuple`\\[`~propositions.syntax.Formula`, ...]):
            the assumptions of the rule.
        conclusion (`~propositions.syntax.Formula`): the conclusion of the rule.
    """

    assumptions: Tuple[Formula, ...]
    conclusion: Formula

    def __init__(self, assumptions: Sequence[Formula], conclusion: Formula):
        """Initializes an `InferenceRule` from its assumptions and conclusion.

        Parameters:
            assumptions: the assumptions for the rule.
            conclusion: the conclusion for the rule.
        """
        self.assumptions = tuple(assumptions)
        self.conclusion = conclusion

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes a string representation of the current inference rule.

        Returns:
            A string representation of the current inference rule.
        """
        return (
            str([str(assumption) for assumption in self.assumptions])
            + " ==> "
            + "'"
            + str(self.conclusion)
            + "'"
        )

    def __eq__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is an `InferenceRule` object that
            equals the current inference rule, ``False`` otherwise.
        """
        return (
            isinstance(other, InferenceRule)
            and self.assumptions == other.assumptions
            and self.conclusion == other.conclusion
        )

    def __ne__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not an `InferenceRule` object or
            does not does not equal the current inference rule, ``False``
            otherwise.
        """
        return not self == other

    # make it be Hashable
    def __hash__(self) -> int:
        return hash(str(self))

    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current inference
        rule.

        Returns:
            A set of all atomic propositions used in the assumptions and in the
            conclusion of the current inference rule.
        """
        # Task 4.1
        return {
            var
            for formula in (self.assumptions + (self.conclusion,))
            for var in Formula.variables(formula)
        }

    def specialize(
        self, specialization_map: SpecializationMap
    ) -> InferenceRule:
        """Specializes the current inference rule by simultaneously substituting
        each variable `v` that is a key in `specialization_map` with the
        formula `specialization_map[v]`.

        Parameters:
            specialization_map: mapping defining the specialization to be
                performed.

        Returns:
            The resulting inference rule.
        """
        for variable in specialization_map:
            assert is_variable(variable)
        # Task 4.4
        substituted_assumptions: Tuple[Formula, ...] = tuple(
            formula.substitute_variables(specialization_map)
            for formula in self.assumptions
        )
        substituted_coclusion: Formula = self.conclusion.substitute_variables(
            specialization_map
        )

        return InferenceRule(substituted_assumptions, substituted_coclusion)

    @staticmethod
    def _merge_specialization_maps(
        specialization_map1: Optional[SpecializationMap],
        specialization_map2: Optional[SpecializationMap],
    ) -> Optional[SpecializationMap]:
        """Merges the given specialization maps while checking their
        consistency.

        Parameters:
            specialization_map1: first mapping to merge, or ``None``.
            specialization_map2: second mapping to merge, or ``None``.

        Returns:
            A single mapping containing all (key, value) pairs that appear in
            either of the given maps, or ``None`` if one of the given maps is
            ``None`` or if some key appears in both given maps but with
            different values.
        """
        if specialization_map1 is not None:
            for variable in specialization_map1:
                assert is_variable(variable), "Only variables can be mapped."
        if specialization_map2 is not None:
            for variable in specialization_map2:
                assert is_variable(variable), "Only variables can be mapped."
        # Task 4.5a

        if specialization_map1 is None or specialization_map2 is None:
            return None

        common_keys: Set[str] = set(specialization_map1.keys()) & set(
            specialization_map2.keys()
        )
        if any(
            specialization_map1[k] != specialization_map2[k]
            for k in common_keys
        ):
            return None
        return {**specialization_map1, **specialization_map2}

    @staticmethod
    def _formula_specialization_map(
        general: Formula, specialization: Formula
    ) -> Optional[SpecializationMap]:
        """Computes the minimal specialization map by which the given formula
        specializes to the given specialization.

        Parameters:
            general: non-specialized formula for which to compute the map.
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of `general`.
        """
        # Task 4.5b

        if is_operator(general.root) and is_operator(specialization.root):
            if general.root == specialization.root:
                if is_binary(general.root):
                    return InferenceRule._merge_specialization_maps(
                        InferenceRule._formula_specialization_map(
                            general.first, specialization.first  # type: ignore
                        ),
                        InferenceRule._formula_specialization_map(
                            general.second, specialization.second  # type: ignore
                        ),
                    )
                if is_unary(general.root):
                    return InferenceRule._formula_specialization_map(
                        general.first, specialization.first  # type: ignore
                    )
                return {}  # T -> T / F -> F is redundant
            return None
        if is_variable(general.root) and is_variable(specialization.root):
            return {general.root: Formula(specialization.root)}
        if is_variable(general.root) and is_operator(specialization.root):
            return {general.root: specialization}
        return None

    def specialization_map(
        self, specialization: InferenceRule
    ) -> Optional[SpecializationMap]:
        """Computes the minimal specialization map by which the current
        inference rule specializes to the given specialization.

        Parameters:
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of the current rule.
        """
        # Task 4.5c
        specialization_map: Optional[SpecializationMap] = dict()

        if len(self.assumptions) != len(specialization.assumptions):
            return None

        for grule, srule in zip(
            self.assumptions + (self.conclusion,),
            specialization.assumptions + (specialization.conclusion,),
        ):
            specialization_map = InferenceRule._merge_specialization_maps(
                specialization_map,
                InferenceRule._formula_specialization_map(grule, srule),
            )

        return specialization_map if specialization_map else None

    def is_specialization_of(self, general: InferenceRule) -> bool:
        """Checks if the current inference rule is a specialization of the given
        inference rule.

        Parameters:
            general: non-specialized inference rule to check.

        Returns:
            ``True`` if the current inference rule is a specialization of
            `general`, ``False`` otherwise.
        """
        return general.specialization_map(self) is not None


@frozen
class Proof:
    """An immutable deductive proof in Propositional Logic, comprised of a
    statement in the form of an inference rule, a set of inference rules that
    may be used in the proof, and a list of lines that prove the statement via
    these inference rules.

    Attributes:
        statement (`InferenceRule`): the statement of the proof.
        rules (`~typing.AbstractSet`\\[`InferenceRule`]): the allowed rules of
            the proof.
        lines (`~typing.Tuple`\\[`Line`]): the lines of the proof.
    """

    statement: InferenceRule
    rules: FrozenSet[InferenceRule]
    lines: Tuple[Proof.Line, ...]

    def __init__(
        self,
        statement: InferenceRule,
        rules: AbstractSet[InferenceRule],
        lines: Sequence[Proof.Line],
    ):
        """Initializes a `Proof` from its statement, allowed inference rules,
        and lines.

        Parameters:
            statement: the statement for the proof.
            rules: the allowed rules for the proof.
            lines: the lines for the proof.
        """
        self.statement = statement
        self.rules = frozenset(rules)
        self.lines = tuple(lines)

    @frozen
    class Line:
        """An immutable line in a deductive proof, comprised of a formula that
        is either justified as an assumption of the proof, or as the conclusion
        of a specialization of an allowed inference rule of the proof, the
        assumptions of which are justified by previous lines in the proof.

        Attributes:
            formula (`~propositions.syntax.Formula`): the formula justified by
                the line.
            rule (`~typing.Optional`\\[`InferenceRule`]): the inference rule,
                out of those allowed in the proof, that has a specialization
                that concludes the formula; or ``None`` if the formula is
                justified as an assumption of the proof.
            assumptions
                (`~typing.Optional`\\[`~typing.Tuple`\\[`int`]): tuple of zero
                or more numbers of previous lines in the proof whose formulas
                are the respective assumptions of the specialization of the rule
                that concludes the formula, if the formula is not justified as
                an assumption of the proof.
        """

        formula: Formula
        rule: Optional[InferenceRule]
        assumptions: Optional[Tuple[int, ...]]

        def __init__(
            self,
            formula: Formula,
            rule: Optional[InferenceRule] = None,
            assumptions: Optional[Sequence[int]] = None,
        ):
            """Initializes a `~Proof.Line` from its formula, and optionally its
            rule and numbers of justifying previous lines.

            Parameters:
                formula: the formula to be justified by the line.
                rule: the inference rule, out of those allowed in the proof,
                    that has a specialization that concludes the formula; or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
                assumptions: numbers of previous lines in the proof whose
                    formulas are the respective assumptions of the
                    specialization of the rule that concludes the formula, or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
            """
            assert (rule is None and assumptions is None) or (
                rule is not None and assumptions is not None
            )
            self.formula = formula
            self.rule = rule
            if assumptions is not None:
                self.assumptions = tuple(assumptions)

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            if self.rule is None:
                return str(self.formula)
            else:
                r = str(self.formula) + "    (Inference Rule " + str(self.rule)
                if len(self.assumptions) == 1:
                    r += " on line " + str(self.assumptions[0])
                elif len(self.assumptions) > 1:
                    r += " on lines " + ",".join(map(str, self.assumptions))
                r += ")"
                return r

        def is_assumption(self) -> bool:
            """Checks if the current proof line is justified as an assumption of
            the proof.

            Returns:
                ``True`` if the current proof line is justified as an assumption
                of the proof, ``False`` otherwise.
            """
            return self.rule is None

    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = "Proof of " + str(self.statement) + " via inference rules:\n"
        for rule in self.rules:
            r += "  " + str(rule) + "\n"
        r += "Lines:\n"
        for i in range(len(self.lines)):
            r += ("%3d) " % i) + str(self.lines[i]) + "\n"
        r += "QED\n"
        return r

    def rule_for_line(self, line_number: int) -> Optional[InferenceRule]:
        """Computes the inference rule whose conclusion is the formula justified
        by the specified line, and whose assumptions are the formulas justified
        by the lines specified as the assumptions of that line.

        Parameters:
            line_number: number of the line according to which to compute the
                inference rule.

        Returns:
            The computed inference rule, with assumptions ordered in the order
            of their numbers in the specified line, or ``None`` if the specified
            line is justified as an assumption.
        """
        assert line_number < len(self.lines)
        # Task 4.6a
        specified_line: Proof.Line = self.lines[line_number]
        if specified_line.is_assumption():
            return None

        rule_assumptions: Tuple[Formula, ...] = tuple(
            self.lines[assumption_no].formula
            for assumption_no in specified_line.assumptions  # type: ignore
        )

        return InferenceRule(rule_assumptions, self.lines[line_number].formula)

    def is_line_valid(self, line_number: int) -> bool:
        """Checks if the specified line validly follows from its justifications.

        Parameters:
            line_number: number of the line to check.

        Returns:
            If the specified line is justified as an assumption, then ``True``
            if the formula justified by this line is an assumption of the
            current proof, ``False`` otherwise. Otherwise (i.e., if the
            specified line is justified as a conclusion of an inference rule),
            ``True`` if the rule specified for that line is one of the allowed
            inference rules in the current proof, and it has a specialization
            that satisfies all of the following:

            1. The conclusion of that specialization is the formula justified by
               that line.
            2. The assumptions of this specialization are the formulas justified
               by the lines that are specified as the assumptions of that line
               (in the order of their numbers in that line), all of which must
               be previous lines.
        """
        assert line_number < len(self.lines)
        # Task 4.6b
        line_to_check: Proof.Line = self.lines[line_number]
        if line_to_check.rule is None:  # Treated as an assumption
            return (
                True
                if line_to_check.formula in self.statement.assumptions
                else False
            )

        line_implied_by_rule: InferenceRule = line_to_check.rule
        line_rule: InferenceRule = self.rule_for_line(line_number)  # type: ignore
        line_assumptions: Tuple[int, ...] = line_to_check.assumptions  # type: ignore

        if (
            line_implied_by_rule in self.rules
            and all(
                line_number > line_assumption
                for line_assumption in line_assumptions
            )
            and (
                not line_assumptions
                or line_rule.is_specialization_of(line_implied_by_rule)
            )
        ):
            return line_rule.is_specialization_of(line_implied_by_rule)
        return False

    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed statement
        via its inference rules.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            statement via its inference rules, ``False`` otherwise.
        """
        # Task 4.6c


# Chapter 5 tasks


def prove_specialization(proof: Proof, specialization: InferenceRule) -> Proof:
    """Converts the given proof of an inference rule to a proof of the given
    specialization of that inference rule.

    Parameters:
        proof: valid proof to convert.
        specialization: specialization of the conclusion of the given proof.

    Returns:
        A valid proof of the given specialization via the same inference rules
        as the given proof.
    """
    assert proof.is_valid()
    assert specialization.is_specialization_of(proof.statement)
    # Task 5.1


def _inline_proof_once(
    main_proof: Proof, line_number: int, lemma_proof: Proof
) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating the usage of (a specialization of)
    that "lemma" rule in the specified line in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        line_number: number of the line in `main_proof` that should be replaced.
        lemma_proof: valid proof of the inference rule of the specified line (an
            allowed inference rule of `main_proof`).

    Returns:
        A valid proof obtained by replacing the specified line in `main_proof`
        with a full (specialized) list of lines proving the formula of the
        specified line from the lines specified as the assumptions of that line,
        and updating justification line numbers specified throughout the proof
        to maintain the validity of the proof. The set of allowed inference
        rules in the returned proof is the union of the rules allowed in the two
        given proofs, but the "lemma" rule that is used in the specified line in
        `main_proof` is no longer used in the corresponding lines in the
        returned proof (and thus, this "lemma" rule is used one less time in the
        returned proof than in `main_proof`).
    """
    assert main_proof.lines[line_number].rule == lemma_proof.statement
    assert lemma_proof.is_valid()
    # Task 5.2a


def inline_proof(main_proof: Proof, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating all usages of (any specialization
    of) that "lemma" rule in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        lemma_proof: valid proof of one of the allowed inference rules of
            `main_proof`.

    Returns:
        A valid proof obtained from `main_proof` by inlining (an appropriate
        specialization of) `lemma_proof` in lieu of each line that specifies the
        "lemma" inference rule proved by `lemma_proof` as its justification. The
        set of allowed inference rules in the returned proof is the union of the
        rules allowed in the two given proofs but without the "lemma" rule
        proved by `lemma_proof`.
    """
    # Task 5.2b
