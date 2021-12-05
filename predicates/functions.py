# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: predicates/functions.py

"""Syntactic conversion of predicate-logic formulas to not use functions and
equality."""

from collections import defaultdict
from functools import reduce
from re import compile as re_compile
from typing import AbstractSet, Dict, List, Pattern, Set

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
        compiled_arg for compiled_arg in compiled_args
    )
    match_till_equal_sign: Pattern[str] = re_compile("[^=]*")

    return former_compiled_args + [
        Formula(
            "=",
            (
                Term(next(fresh_variable_name_generator)),
                Term(
                    term.root,
                    tuple(
                        arg
                        if not is_function(arg.root)
                        else Term(  # z1=... -> z1 ; x12 -> x12
                            match_till_equal_sign.match(
                                str(next(steps_gen))
                            ).group(0)
                        )
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
                for function, _ in formula.functions()
            }.intersection({relation for relation, _ in formula.relations()})
        )
        == 0
    )
    for variable in formula.variables():
        assert variable[0] != "z"
    # Task 8.4

    if is_relation(formula.root) or is_equality(formula.root):
        compiled_terms: List[Formula] = []
        rel_or_eq_new_args: List[Term] = []

        for arg in formula.arguments:
            if is_function(arg.root):
                compiled_terms.extend(_compile_term(arg))
                rel_or_eq_new_args.append(compiled_terms[-1].arguments[0])
            else:
                rel_or_eq_new_args.append(arg)

        return compiled_terms_to_conjuctive_relations(
            compiled_terms, formula.root, rel_or_eq_new_args
        )
    else:  # Var/Constant / Unary / Binary / Quantification
        first: Formula
        second: Formula

        if is_constant(formula.root) or is_variable(formula.root):
            return formula
        elif is_unary(formula.root):
            first = replace_functions_with_relations_in_formula(formula.first)
        elif is_binary(formula.root):
            first = replace_functions_with_relations_in_formula(formula.first)
            second = replace_functions_with_relations_in_formula(formula.second)
        else:  # Quantification
            first = formula.variable
            second = replace_functions_with_relations_in_formula(
                formula.statement
            )

        return Formula(formula.root, first, second)


def compiled_terms_to_conjuctive_relations(
    compiled_terms: List[Formula],
    rel_name_or_equality: str,
    rel_or_eq_args: List[Term],
) -> Formula:
    if not compiled_terms:
        return Formula(
            rel_name_or_equality,
            rel_or_eq_args,
        )

    curr_compiled_term: Formula = compiled_terms[0]
    term_value: Term = curr_compiled_term.arguments[0]

    return Formula(
        "E",
        term_value.root,
        Formula(
            "&",
            compiled_term_to_relation(compiled_terms[0]),
            compiled_terms_to_conjuctive_relations(
                compiled_terms[1:], rel_name_or_equality, rel_or_eq_args
            ),
        ),
    )


def compiled_term_to_relation(compiled_term: Formula) -> Formula:
    assert compiled_term

    curr_compiled_term: Formula = compiled_term
    term_value: Term = curr_compiled_term.arguments[0]
    compiled_term_associated_func: Term = curr_compiled_term.arguments[1]

    return Formula(
        compiled_term_associated_func.root.upper(),
        (term_value, *compiled_term_associated_func.arguments),
    )


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
                        for function, _ in formula.functions()
                    }
                    for formula in formulas
                ]
            ).intersection(
                set.union(
                    *[
                        {relation for relation, _ in formula.relations()}
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

    free_func_formulas: Set[Formula] = reduce(
        lambda s1, s2: s1.union(s2),
        list(
            {replace_functions_with_relations_in_formula(formula)}
            for formula in formulas
        ),
    )

    omitted_funcs: List[Tuple[str, int]] = list(
        reduce(
            lambda s1, s2: s1.union(s2),
            (formula.functions() for formula in formulas),
        )
    )

    for omitted_func in omitted_funcs:
        free_func_formulas.add(
            func_to_functionalized_relation(
                omitted_func[0].upper(), omitted_func[1]
            )
        )

    return free_func_formulas


def func_to_functionalized_relation(
    func_to_rel_name: str, arity: int
) -> Formula:
    return Formula(
        "&",
        domain_to_codomain(func_to_rel_name, arity),
        domain_to_unique_codomain(func_to_rel_name, arity),
    )


def domain_to_codomain(func_to_rel_name: str, arity: int) -> Formula:
    if arity == 1:
        arg: str = next(fresh_variable_name_generator)
        val: str = next(fresh_variable_name_generator)

        return Formula(
            "A",
            arg,
            Formula(
                "E", val, Formula(func_to_rel_name, [Term(val), Term(arg)])
            ),
        )

    return Formula(
        "A",
        next(fresh_variable_name_generator),
        func_to_functionalized_relation(func_to_rel_name, arity - 1),
    )


def domain_to_unique_codomain(func_to_rel_name: str, arity: int) -> Formula:
    first_val: Term = Term(next(fresh_variable_name_generator))
    second_val: Term = Term(next(fresh_variable_name_generator))

    args: List[Term] = [
        Term(next(fresh_variable_name_generator)) for _ in range(arity)
    ]

    first_rel: Formula = Formula(func_to_rel_name, [first_val, *args])
    second_rel: Formula = Formula(func_to_rel_name, [second_val, *args])

    return Formula(
        "->",
        Formula(
            "A",
            first_val.root,
            Formula("A", second_val.root, Formula("&", first_rel, second_rel)),
        ),
        Formula("=", [first_val, second_val]),
    )


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
        assert "SAME" not in {relation for relation, _ in formula.relations()}
    # Task 8.6

    equality_to_SAME: List[Formula] = list()

    SAME_reflexive: Formula = Formula.parse("Ax[SAME(x,x)]")
    SAME_symmetric: Formula = Formula.parse("Ax[Ay[(SAME(x,y)->SAME(y,x))]]")
    SAME_transitive: Formula = Formula.parse(
        "Ax[Ay[Az[((SAME(x,y)&SAME(y,z))->SAME(x,z))]]]"
    )

    equality_to_SAME.extend(
        [
            SAME_reflexive,
            SAME_symmetric,
            SAME_transitive,
            *(
                syntactic_equality_to_SAME_relation(formula)
                for formula in formulas
            ),
        ]
    )

    for formula in formulas:
        for relation in formula.relations():
            equality_to_SAME.append(
                (
                    equality_meaning_in_relation(relation[0], relation[1])
                    if relation[1] > 0
                    else Formula(relation[0], [])
                )
            )

    return {free_equality_formula for free_equality_formula in equality_to_SAME}


# TODO - Yikes!!! Make it Pythonic!
def equality_meaning_in_relation(rel_name: str, arity: int) -> Formula:
    xs: List[str] = [next(fresh_variable_name_generator) for _ in range(arity)]
    ys: List[str] = [next(fresh_variable_name_generator) for _ in range(arity)]

    formula_as_string: str = str()

    for arg in xs + ys:
        formula_as_string += "A" + arg + "["

    SAMES: List[str] = list()
    for x, y in zip(xs, ys):
        SAMES.append(f"SAME({x},{y})")
    formula_as_string += "(" + SAME_conjuction(SAMES) + "->("

    R1_implies: str = fr"{rel_name}({','.join(xs)})->"
    R2: str = fr"{rel_name}({','.join(ys)})))"

    formula_as_string += R1_implies + R2 + "]" * arity * 2

    return Formula.parse(formula_as_string)


def SAME_conjuction(SAME_relations: List[str]) -> str:
    if len(SAME_relations) == 1:
        return SAME_relations[0]

    return f"({SAME_relations[0]}&{SAME_conjuction(SAME_relations[1:])})"


def syntactic_equality_to_SAME_relation(
    formula: Formula,
) -> Formula:
    if is_equality(formula.root):
        return Formula("SAME", formula.arguments)

    if is_quantifier(formula.root):
        return Formula(
            formula.root,
            formula.variable,
            syntactic_equality_to_SAME_relation(formula.statement),
        )

    if is_unary(formula.root):
        return Formula(
            formula.root, syntactic_equality_to_SAME_relation(formula.first)
        )

    if is_binary(formula.root):
        return Formula(
            formula.root,
            syntactic_equality_to_SAME_relation(formula.first),
            syntactic_equality_to_SAME_relation(formula.second),
        )

    return formula  # Constant / Var / Relation


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

    return Model(
        model.universe,
        model.constant_interpretations,
        {
            **model.relation_interpretations,
            "SAME": {(atom, atom) for atom in model.universe},
        },
        model.function_interpretations,
    )


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

    equivalent_classes: List[Set[T]] = []

    def eq_class_of_val(val: T) -> Optional[Set[T]]:
        return next((cl for cl in equivalent_classes if val in cl), None)

    def get_repr(el: T) -> T:
        if el in eq_representatives.keys():  # is representative
            return el

        return next(
            repr
            for repr in eq_representatives.keys()
            if el in eq_representatives[repr]
        )

    for l_val, r_val in model.relation_interpretations["SAME"]:
        l_cl: Optional[Set[T]] = eq_class_of_val(l_val)
        r_cl: Optional[Set[T]] = eq_class_of_val(r_val)

        if l_cl is not None and r_cl is not None and l_cl is not r_cl:
            l_cl.update(r_cl)  # type: ignore
            equivalent_classes.remove(r_cl)  # type: ignore
        elif l_cl is not None:
            l_cl.add(r_val)
        else:
            equivalent_classes.append({l_val, r_val})

    eq_representatives: Dict[T, Set[T]] = {
        cl.pop(): cl for cl in equivalent_classes
    }
    new_universe: Set[T] = {repr for repr in eq_representatives.keys()}

    new_constants: Dict[str, T] = {
        const: get_repr(el)
        for const, el in model.constant_interpretations.items()
    }

    new_relations: Dict[str, AbstractSet[Tuple[T, ...]]] = {
        rel: {tup for tup in rel_tupls if set(tup) <= new_universe}
        for rel, rel_tupls in model.relation_interpretations.items()
        if rel != "SAME"
    }

    return Model(
        new_universe,
        new_constants,
        new_relations,
        model.function_interpretations,
    )
