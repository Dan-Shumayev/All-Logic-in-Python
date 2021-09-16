# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from itertools import product as it_product
from typing import AbstractSet, Iterable, List, Mapping, Sequence

from .proofs import *
from .syntax import *

#: A model for propositional-logic formulas, a mapping from variable names to
#: truth values.
Model = Mapping[str, bool]

# constants
NEWLINE: str = "\n"
TRUTH_TAB_SEP: str = "|"
WHITESPACE_SEP: str = " "


def is_model(model: Model) -> bool:
    """Checks if the given dictionary is a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not is_variable(key):
            return False
    return True


def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()


def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.

    Examples:
        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
        True

        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
        False
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1
    if is_constant(formula.root):
        return True if formula.root == "T" else False
    if is_variable(formula.root):
        return model[formula.root]
    if is_unary(formula.root):
        return not evaluate(formula.first, model)  # type: ignore

    return evaluate_binary_formula(formula, model)


def evaluate_binary_formula(formula: Formula, model: Model) -> bool:
    """Evaluates the value of a binary formula.

    Parameters:
        formula: the formula to evaluate.
        model: the model we evaluate with respect to.

    Returns:
        If (φ = ε • ψ), then φ's value is True iff the value of
        (either - |/both - &) ε and ψ is True in M.
        If (φ = ψ -> ε), then φ's value is True if either φ (in M)
        False or if the value of ε (in M) is True.
    """
    binary_op: str = formula.root  # & | ->
    if binary_op == "&":
        return evaluate(formula.first, model) and evaluate(formula.second, model)  # type: ignore
    if binary_op == "|":
        return evaluate(formula.first, model) or evaluate(formula.second, model)  # type: ignore
    # ->
    return not evaluate(formula.first, model) or evaluate(formula.second, model)  # type: ignore


def all_models(variables: Sequence[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True},
         {'p': True, 'q': False}, {'p': True, 'q': True}]

        >>> list(all_models(['q', 'p']))
        [{'q': False, 'p': False}, {'q': False, 'p': True},
         {'q': True, 'p': False}, {'q': True, 'p': True}]
    """
    for v in variables:
        assert is_variable(v)
    # Task 2.2
    permutations = it_product([False, True], repeat=len(variables))
    for permutation in permutations:
        possible_model: Model = {
            var: permutation[index] for index, var in enumerate(variables)
        }
        yield possible_model


def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.

    Examples:
        >>> list(truth_values(Formula.parse('~(p&q76)'), all_models(['p', 'q76'])))
        [True, True, True, False]
    """
    # Task 2.3
    for model in models:
        yield evaluate(formula, model)


def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4

    formula_variables: List[str] = list(formula.variables())
    formula_variables.sort()  # Variables are sorted at the first row

    formula_to_string: str = Formula.formula_obj_to_string(formula)

    # First row:
    print_variables_row(formula_variables, formula_to_string)

    # Line-separator:
    print_line_separator(formula_variables, formula_to_string)

    # Table values:
    print_table_values(
        formula_variables,
        formula,
        formula_to_string,
    )


def print_table_values(
    formula_variables,
    formula,
    formula_to_string,
) -> None:
    """Prints the cells of the truth table. These rows contain the evaluation of each
    variable variable in respect to a possible model. Also, the last column
    contains the value of the entire formula using the variables' value.

    Parameters:
        formula_variables: The formula variables.
        TRUTH_TAB_SEP: The separator symbol of the table.
        WHITESPACE_SEP: Some amount of whitespaces between each cell.
        formula: The formula to evaluate.
        formula_to_string: The string repr. of the formula.
    """
    BOOL_TO_STR: Mapping[bool, str] = {True: "T", False: "F"}

    for model in all_models(formula_variables):
        for variable, value in model.items():
            print_table_row(
                TRUTH_TAB_SEP + WHITESPACE_SEP,
                BOOL_TO_STR[value],
                WHITESPACE_SEP * len(variable),
            )
        formula_value: bool = evaluate(formula, model)
        print_table_row(
            TRUTH_TAB_SEP + WHITESPACE_SEP,
            BOOL_TO_STR[formula_value],
            WHITESPACE_SEP * len(formula_to_string) + TRUTH_TAB_SEP + NEWLINE,
        )


def print_line_separator(formula_variables, formula_to_string) -> None:
    """Prints the second row of the truth table. This rows contains only some delimiter
    to separate between the variables and their evaluation.

    Parameters:
        TRUTH_TAB_SEP: The separator symbol of the table.
        formula_variables: The formula variables.
        formula_to_string: The string repr. of the formula.
    """
    LINE_SEP_SYM: str = "-"

    print_table_row("", TRUTH_TAB_SEP)
    for variable in formula_variables:
        col_width: int = len(variable) + 2
        print_table_row("", LINE_SEP_SYM * col_width, TRUTH_TAB_SEP)
    formula_col_width: int = len(formula_to_string) + 2
    print_table_row(
        "", LINE_SEP_SYM * formula_col_width, TRUTH_TAB_SEP + NEWLINE
    )


def print_variables_row(formula_variables, formula_to_string: str) -> None:
    """Prints the first row of the truth table. This rows contains the formula
    variables as well as the formula itself.

    Parameters:
        formula_variables: The formula variables.
        formula_to_string: The string repr. of the formula.
        TRUTH_TAB_SEP: The separator symbol of the table.
        WHITESPACE_SEP: Some amount of whitespaces between each cell.
    """
    for variable in formula_variables:
        print_table_row(
            TRUTH_TAB_SEP + WHITESPACE_SEP, variable, WHITESPACE_SEP
        )
    print_table_row(
        TRUTH_TAB_SEP + WHITESPACE_SEP,
        formula_to_string,
        WHITESPACE_SEP + TRUTH_TAB_SEP + NEWLINE,
    )


def print_table_row(prefix: str, string: str, suffix: str = "") -> None:
    """Prints a string without a newline.

    Parameters:
        string: The string to print.
    """
    print(prefix + string, end=suffix)


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a
    return contradiction_or_tautology(
        formula, contradiction=False, tautology=True
    )


def contradiction_or_tautology(
    formula: Formula, contradiction=True, tautology=False
) -> bool:
    """Evaluates if the formula is either a contradiction or a tautology,
    but not both.

        Parameters:
            formula: The formula to evaluate.
            contradiction: ``True``` iff we check the formula for a contradiction.
            tautology: ``True``` iff we check the formula for a tautology.

        Returns:
        ``True``` iff the formula evaluates to a contradiction/tautology according
        to the chosen mode.
    """
    assert contradiction != tautology, "You have to choose a single mode."
    formula_variables: List[str] = list(formula.variables())

    for model in all_models(formula_variables):
        evaluated = evaluate(formula, model)

        if (contradiction and evaluated) or (tautology and not evaluated):
            return False

    return True


def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    return contradiction_or_tautology(formula, contradiction=True)


def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c
    return not is_contradiction(formula)


def _synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single conjunctive
    clause that evaluates to ``True`` in the given model, and to ``False`` in
    any other model over the same variables.

    Parameters:
        model: model over a nonempty set of variables, in which the synthesized
            formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Task 2.6
    NEGATE_SYM: str = "~"
    BINARY_AND: str = "&"

    def trutify_var(var: str) -> Formula:
        return (
            Formula(NEGATE_SYM, Formula(var, None, None), None)
            if not model[var]
            else Formula(var, None, None)
        )

    # Convert the model dict into a list of respective tuples:
    model_as_tuples: List[Tuple] = list(model.items())

    current_formula: Formula = trutify_var(model_as_tuples[0][0])

    for var, _ in model_as_tuples[
        1:
    ]:  # Skip over the first variable we've just evaluted
        current_formula = Formula(BINARY_AND, current_formula, trutify_var(var))

    return current_formula


def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variables for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7
    models_to_dnf: List[Model] = list()

    # In case the formula is always ``False`` => The formula is simply OR over
    # all the variables
    there_is_true: bool = False
    for val in values:
        there_is_true |= val
    if not there_is_true:
        var_formula: Formula = Formula(variables[0], None, None)
        current_formula: Formula = Formula(
            "&", var_formula, Formula("~", var_formula, None)
        )
        for var in variables[1:]:
            var_formula_another: Formula = Formula(var, None, None)
            current_formula = Formula(
                "|",
                current_formula,
                Formula(
                    "&",
                    var_formula_another,
                    Formula("~", var_formula_another, None),
                ),
            )
        return current_formula

    for (model, value) in zip(all_models(variables), values):
        if value:
            models_to_dnf.append(model)

    dnf_formulas: List[Formula] = []
    for model in models_to_dnf:
        first_var: str = variables[0]
        intermediate_formula: Formula = (
            Formula(first_var, None, None)
            if model[first_var]
            else Formula("~", Formula(first_var, None, None), None)
        )
        for var in variables[1:]:
            intermediate_formula = (
                Formula("&", intermediate_formula, Formula(var, None, None))
                if model[var]
                else Formula(
                    "&",
                    intermediate_formula,
                    Formula("~", Formula(var, None, None), None),
                )
            )
        dnf_formulas.append(intermediate_formula)
    current_dnf_formula: Formula = dnf_formulas[0]
    for dnf_formula in dnf_formulas:
        current_dnf_formula = Formula("|", current_dnf_formula, dnf_formula)

    return current_dnf_formula


def _synthesize_for_all_except_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single disjunctive
    clause that evaluates to ``False`` in the given model, and to ``True`` in
    any other model over the same variables.

    Parameters:
        model: model over a nonempty set of variables, in which the synthesized
            formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Optional Task 2.8


def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in CNF over the given variables,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variables for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize_cnf(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Optional Task 2.9


# Tasks for Chapter 4


def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.

    Examples:
        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': True, 'q': False})
        False

        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': False, 'q': False})
        True
    """
    assert is_model(model)
    # Task 4.2


def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
