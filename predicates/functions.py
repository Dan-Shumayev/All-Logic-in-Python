# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: predicates/functions.py

"""Syntactic conversion of predicate-logic formulas to not use functions and
equality."""

from collections import defaultdict
from re import match as re_match
from typing import AbstractSet, Dict, List, Set

from logic_utils import fresh_variable_name_generator

from predicates.semantics import *
from predicates.syntax import *


def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]


def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]


def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function interpretations, replacing each function interpretation with a
    canonically corresponding relation interpretation.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            interpretations in this model.

    Returns:
        A model obtained from the given model by replacing every function
        interpretation of a function name with a relation interpretation of the
        canonically corresponding relation name, such that the relation
        interpretation contains any tuple
        ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1` is the
        output of the function interpretation for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_interpretations:
        assert (
            function_name_to_relation_name(function)
            not in model.relation_interpretations
        )
    # Task 8.1

    new_relations: RelationInterpretation = model.relation_interpretations

    for func_name, func_inter in model.function_interpretations.items():
        new_relations = {
            **new_relations,
            **{
                function_name_to_relation_name(func_name): {
                    (v, *k) for k, v in func_inter.items()
                }
            },
        }

    return Model(
        model.universe,
        model.constant_interpretations,
        new_relations,
    )


def is_legal_relations_to_functions(
    model: Model[T], function_names_as_relations: List[str]
) -> bool:
    def doesExistFunctionWithoutRelation() -> bool:
        return any(
            func_name not in model.relation_interpretations.keys()
            for func_name in function_names_as_relations
        )

    def doesExistIllegalRelationToFunction() -> bool:
        for func_name in function_names_as_relations:

            relation_as_func: RelationType = model.relation_interpretations[
                func_name
            ]

            func_vals: List[T] = list(tupl[0] for tupl in relation_as_func)

            func_actual_args: List[Tuple[T, ...]] = list(
                tupl[1:] for tupl in relation_as_func
            )

            func_required_args: List[Tuple[T, ...]] = list(
                it_product(
                    model.universe,
                    repeat=model.relation_arities[func_name] - 1,
                )
            )

            if (
                not set(func_vals).issubset(model.universe)
                or len(func_actual_args) != len(func_required_args)
                or set(func_actual_args) != set(func_required_args)
            ):
                return True

        return False

    return not (
        doesExistFunctionWithoutRelation()
        or doesExistIllegalRelationToFunction()
    )


def replace_relations_with_functions_in_model(
    model: Model[T], original_functions: AbstractSet[str]
) -> Union[Model[T], None]:
    """Converts the given model with no function interpretations to a
    canonically corresponding model with interpretations for the given function
    names, having each new function interpretation replace a canonically
    corresponding relation interpretation.

    Parameters:
        model: model to convert, that contains no function interpretations.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has an interpretation in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    assert len(model.function_interpretations) == 0
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_interpretations
        assert (
            function_name_to_relation_name(function)
            in model.relation_interpretations
        )
    # Task 8.2

    function_names_to_relation_names: Dict[str, str] = {
        func_name: function_name_to_relation_name(func_name)
        for func_name in original_functions
    }

    if not is_legal_relations_to_functions(
        model, list(function_names_to_relation_names.values())
    ):
        return None

    replaced_relations_as_functions: FunctionInterpretation = defaultdict(dict)

    for func_name, func_as_rel in function_names_to_relation_names.items():
        replaced_relations_as_functions[func_name] = {
            tupl[1:]: tupl[
                0
            ]  # We assume the relations always have at least one arg, because it's
            # required for functions
            for tupl in model.relation_interpretations[func_as_rel]
        }

    left_relations: RelationInterpretation = dict(
        filter(
            lambda relation: relation[0]
            not in function_names_to_relation_names.values(),
            model.relation_interpretations.items(),
        )
    )

    return Model(
        model.universe,
        model.constant_interpretations,
        left_relations,
        replaced_relations_as_functions,
    )


def _compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and which
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable name of the
        last returned step evaluates in that model to the value of the given
        term.
    """
    assert is_function(term.root) and term.arguments
    for variable in term.variables():
        assert variable[0] != "z"
    # Task 8.3

    former_compiled_args: List[Formula] = []
    compiled_args: List[Formula] = []

    for arg in term.arguments:
        if is_function(arg.root):
            curr_compiled_arg: List[Formula] = _compile_term(arg)
            former_compiled_args += curr_compiled_arg

            compiled_args.append(curr_compiled_arg[-1])  # Only this term's arg

    steps_gen: Iterator[Formula] = (
        compiled_args for compiled_args in compiled_args
    )
    match_till_equal_sign: str = "[^=]*"

    return former_compiled_args + [
        Formula(
            "=",
            (
                next(fresh_variable_name_generator),
                Term(
                    term.root,
                    tuple(
                        arg
                        if not is_function(arg.root)
                        else re_match(
                            match_till_equal_sign, str(next(steps_gen))
                        ).group(0)
                        for arg in term.arguments
                    ),
                ),
            ),
        )
    ]


def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function interpretations.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert (
        len(
            {
                function_name_to_relation_name(function)
                for function, arity in formula.functions()
            }.intersection(
                {relation for relation, arity in formula.relations()}
            )
        )
        == 0
    )
    for variable in formula.variables():
        assert variable[0] != "z"
    # Task 8.4


def replace_functions_with_relations_in_formulas(
    formulas: AbstractSet[Formula],
) -> Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function interpretations.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with interpretations for the functions
       names of the former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, which contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas hold in a model `model` if and only if the
           returned formulas hold in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas hold in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert (
        len(
            set.union(
                *[
                    {
                        function_name_to_relation_name(function)
                        for function, arity in formula.functions()
                    }
                    for formula in formulas
                ]
            ).intersection(
                set.union(
                    *[
                        {relation for relation, arity in formula.relations()}
                        for formula in formulas
                    ]
                )
            )
        )
        == 0
    )
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != "z"
    # Task 8.5


def replace_equality_with_SAME_in_formulas(
    formulas: AbstractSet[Formula],
) -> Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model of the returned formulas, the
       interpretation of the relation name ``'SAME'`` is reflexive,
       symmetric, and transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model of the returned formulas, the interpretation of this
       relation name respects the interpretation of the relation name
       ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert "SAME" not in {
            relation for relation, arity in formula.relations()
        }
    # Task 8.6


def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds an interpretation of the relation name ``'SAME'`` in the given
    model, that canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no interpretation of the relation name
            ``'SAME'``, to add the interpretation to.

    Returns:
        A model obtained from the given model by adding an interpretation of the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert "SAME" not in model.relation_interpretations
    # Task 8.7


def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    interpretation of ``'SAME'`` in the given model, in the sense that any set
    of formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function interpretations, and
            contains an interpretation of the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the
            interpretations of all other relation names.

    Returns:
        A model that is a model of any set `formulas` if and only if the given
        model is a model of
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        interpretation of ``'SAME'`` in the given model.
    """
    assert (
        "SAME" in model.relation_interpretations
        and model.relation_arities["SAME"] == 2
    )
    assert len(model.function_interpretations) == 0
    # Task 8.8
