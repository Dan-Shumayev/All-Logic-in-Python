# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: predicates/syntax.py

"""Syntactic handling of predicate-logic expressions."""

from __future__ import annotations

from functools import lru_cache
from functools import reduce as ft_reduce
from itertools import chain as it_chain
from operator import attrgetter, methodcaller
from re import compile as re_compile
from typing import (
    AbstractSet,
    Dict,
    Iterator,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from logic_utils import (
    fresh_variable_name_generator,
    frozen,
    memoized_parameterless_method,
)
from propositions.syntax import Formula as PropositionalFormula
from propositions.syntax import is_variable as is_propositional_variable

TermPrefix = Tuple["Term", str]  # "" for Forward Reference
FormulaPrefix = Tuple["Formula", str]  # "" for Forward Reference


class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context.

    Attributes:
        variable_name (`str`): the variable name that was forbidden in the
            context in which a term containing it was to be substituted.
    """

    variable_name: str

    def __init__(self, variable_name: str):
        """Initializes a `ForbiddenVariableError` from the offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it is to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name


@lru_cache(maxsize=100)  # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return (
        (
            (string[0] >= "0" and string[0] <= "9")
            or (string[0] >= "a" and string[0] <= "e")
        )
        and string.isalnum()
    ) or string == "_"


@lru_cache(maxsize=100)  # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= "u" and string[0] <= "z" and string.isalnum()


@lru_cache(maxsize=100)  # Cache the return value of is_function
def is_function(string: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return string[0] >= "f" and string[0] <= "t" and string.isalnum()


# TODO - consider changing the parsing to PyParsing / Recursive-Descent Parser
class TermParser:
    """
    |   Recursive-Descent Parser for Terms represented by First-Order logic.
    |   The grammar:
    |
    |   Var ::= [u-z] possibly followed by a number
    |   Const ::= [0-9a-e][\w*] | _
    |   Func ::= [f-t][\w*](<Term>,<Term>,<Term>,...) - At least one <Term>
    |   Term ::= <Var> | <Const> | <Func>
    """

    # Regexes to match the respective tokens
    VAR_REGEX = re_compile(r"[u-z]+[A-Za-z]*[0-9]*")
    CONST_REGEX = re_compile(r"[0-9a-e][a-zA-Z0-9]*|[_]")
    FUNC_REGEX = re_compile(r"[f-t](\w*)")

    # each parser will return the parsed element, tupled with
    # the remainder of the parsing

    def parse(self, string_to_parse: str) -> TermPrefix:
        """Parses a string to its respective Formula/Term object,
        tupled with its remainder which isn't derived by our logic's grammar.

        Parameters:
            string_to_parse: The string to parse.

        Returns:
            A tuple of Formula/Term object with its string remainder
            if exists (None if not).
        """
        query = methodcaller("match", string_to_parse)
        match = query(TermParser.VAR_REGEX) or query(TermParser.CONST_REGEX)

        if match is not None:  # so you don't get attr error
            return Term(match.group(0)), string_to_parse[match.end(0) :]
        match = query(TermParser.FUNC_REGEX)
        if match is not None:
            return self.parse_function(string_to_parse, match)

        return None, string_to_parse  # type: ignore

    def parse_function(self, string_to_parse: str, matched_func) -> TermPrefix:
        """ """
        assert matched_func, "Expected a function"
        assert (
            string_to_parse[matched_func.end(0)] == "("
        ), "Expected open paren"

        func_name: str = matched_func.group(0)

        left, left_remainder = self.parse(
            string_to_parse[matched_func.end(0) + 1 :]
        )
        assert left, "At least one Term is required inside function."
        assert left_remainder is not None, (
            "Expected either a comma before another Term or end of function"
            " denoted by a close-paren."
        )

        terms: List[Term] = [left]
        while left_remainder.startswith(","):
            left, left_remainder = self.parse(left_remainder[1:])
            if left is None:
                return None, string_to_parse
            terms.append(left)
        if left_remainder.startswith(")"):
            return Term(func_name, terms), left_remainder[1:]

        return None, string_to_parse  # type: ignore


class FormulaParser:
    """
    |   Recursive-Descent Parser for Formulas represented by First-Order Logic.
    |   The grammar:
    |
    |   Var ::= [u-z] possibly followed by a number
    |   Const ::= [0-9a-e][\w*] | _
    |   Func ::= [f-t][\w*](<Term>,<Term>,<Term>,...) - At least one <Term>
    |   Term ::= <Var> | <Const> | <Func>
    |
    |   R ::= [F-T][\w*](<Term>,<Term>,<Term>,...) - Nullary relations allowed
    |   Formula ::= <Term>=<Term> | <R> | ~<Formula> | (Formula*Formula) (where `*`
    |   is one of `|`, `&`, or `->`) | [A|E]<Var>[<Formula>] (where `A` and `E` indicate
    |   the logical quantifiers `∀` and `∃` repectively)
    """

    # Regexes and patterns to match the respective tokens
    TERM_PATTERN = fr"{TermParser.VAR_REGEX.pattern}|{TermParser.FUNC_REGEX.pattern}|{TermParser.CONST_REGEX.pattern}"

    RELATION_REGEX = re_compile(r"[F-T]+[\w\d]*")
    QUANT_REGEX = re_compile(r"[A|E]")
    TERM_REGEX = re_compile(TERM_PATTERN)
    EQ_REGEX = re_compile(fr"{TERM_PATTERN}={TERM_PATTERN}")

    BINARY_REGEX = re_compile(r"->|^&|^\|")

    # each parser will return the parsed element, tupled with
    # the remainder of the parsing

    def parse(self, string_to_parse: str) -> FormulaPrefix:
        """Parses a string to its respective Formula/Term object,
        tupled with its remainder which isn't derived by our logic's grammar.

        Parameters:
            string_to_parse: The string to parse.

        Returns:
            A tuple of Formula/Term object with its string remainder
            if exists (None if not).
        """
        assert string_to_parse

        if is_unary(string_to_parse[0]):
            formula, suffix = self.parse(string_to_parse[1:])
            return Formula("~", formula), suffix
        if string_to_parse.startswith("("):
            return self.parse_binary_formula(string_to_parse[1:])
        if FormulaParser.EQ_REGEX.match(string_to_parse):
            formula1, suffix1 = TermParser().parse(string_to_parse)
            formula2, suffix2 = TermParser().parse(suffix1[1:])
            return Formula("=", (formula1, formula2)), suffix2
        if FormulaParser.QUANT_REGEX.match(string_to_parse):
            return self.parse_quantifier(string_to_parse)
        if FormulaParser.RELATION_REGEX.match(string_to_parse):
            return self.parse_relation(string_to_parse)

        return None, string_to_parse  # type: ignore

    def parse_relation(self, string_to_parse: str) -> FormulaPrefix:
        match = FormulaParser.RELATION_REGEX.match(string_to_parse)
        assert match
        assert string_to_parse[match.end(0)] == "("

        if string_to_parse[match.end(0) + 1] == ")":
            return (
                Formula(match.group(0), []),
                string_to_parse[match.end(0) + 2 :],
            )

        first_term, suffix = TermParser().parse(
            string_to_parse[match.end(0) + 1 :]
        )
        terms: List[Term] = [first_term]
        while suffix.startswith(","):
            term, suffix = TermParser().parse(suffix[1:])
            terms.append(term)
        assert suffix.startswith(")")

        return Formula(match.group(0), terms), suffix[1:]

    def parse_quantifier(self, string_to_parse: str) -> FormulaPrefix:
        """ """
        assert is_quantifier(string_to_parse[0]) and len(string_to_parse) > 1
        var, formula_string = TermParser().parse(string_to_parse[1:])

        assert formula_string[0] == "["
        formula, suffix = self.parse(formula_string[1:])
        assert suffix[0] == "]"

        return Formula(string_to_parse[0], str(var), formula), suffix[1:]

    def parse_binary_formula(self, string_to_parse: str) -> FormulaPrefix:
        """ """
        formula1, suffix1 = self.parse(string_to_parse)
        assert formula1 and suffix1
        op = FormulaParser.BINARY_REGEX.match(suffix1)
        assert op, "Expected binary-op and a second formula."

        formula2, suffix2 = self.parse(suffix1[op.end(0) :])
        return Formula(op.group(0), formula1, formula2), suffix2[1:]


@frozen
class Term:
    """An immutable predicate-logic term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments of the root, if the root is a function name.
    """

    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str, arguments: Optional[Sequence[Term]] = None):
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments for the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None and len(arguments) > 0
            self.root = root
            self.arguments = tuple(arguments)

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        # Task 7.1
        if is_constant(self.root) or is_variable(self.root):
            return self.root
        assert self.arguments
        args: Sequence[str] = [str(arg) for arg in self.arguments]
        return f"{self.root}({','.join(args)})"

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.3a
        return TermParser().parse(string)

    @staticmethod
    def parse(string: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            string: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        # Task 7.3b
        return Term._parse_prefix(string)[0]

    def _dfs_iterator(self) -> Iterator[Term]:
        """Iterates over ALL Terms in DFS"""
        yield self  # Function / Variable / Constant
        if is_function(self.root):
            yield from it_chain.from_iterable(
                term._dfs_iterator() for term in self.arguments  # type: ignore
            )

    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        # Task 7.5a
        return {
            term.root for term in self._dfs_iterator() if is_constant(term.root)
        }

    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        # Task 7.5b
        return {
            term.root for term in self._dfs_iterator() if is_variable(term.root)
        }

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        # Task 7.5c
        return {
            (term.root, len(term.arguments))
            for term in self._dfs_iterator()
            if is_function(term.root)
        }

    @staticmethod
    def is_term(formula_root: str) -> bool:
        return (
            is_function(formula_root)
            or is_constant(formula_root)
            or is_variable(formula_root)
        )

    def substitute(
        self,
        substitution_map: Mapping[str, Term],
        forbidden_variables: AbstractSet[str] = frozenset(),
    ) -> Term:
        """Substitutes in the current term, each constant name `construct` or
        variable name `construct` that is a key in `substitution_map` with the
        term `substitution_map`\ ``[``\ `construct`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variable names not allowed in substitution
                terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant name and variable name occurrences originating in the
            current term are substituted (i.e., those originating in one of the
            specified substitutions are not subjected to additional
            substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable name from
                `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))

            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for construct in substitution_map:
            assert is_constant(construct) or is_variable(construct)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.1

        if is_function(self.root):
            assert self.arguments
            modified_args: List[Term] = [
                arg.substitute(substitution_map, forbidden_variables)
                for arg in self.arguments
            ]

            return Term(self.root, modified_args)

        possible_forbid_vars: Set[
            str
        ] = self.root in substitution_map.keys() and substitution_map[
            self.root
        ].variables().intersection(
            forbidden_variables
        )

        if possible_forbid_vars:
            raise ForbiddenVariableError(possible_forbid_vars.pop())

        return (
            substitution_map[self.root]
            if self.root in substitution_map.keys()
            else Term(self.root)
        )


@lru_cache(maxsize=100)  # Cache the return value of is_equality
def is_equality(string: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return string == "="


@lru_cache(maxsize=100)  # Cache the return value of is_relation
def is_relation(string: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return string[0] >= "F" and string[0] <= "T" and string.isalnum()


@lru_cache(maxsize=100)  # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == "~"


@lru_cache(maxsize=100)  # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return string == "&" or string == "|" or string == "->"


@lru_cache(maxsize=100)  # Cache the return value of is_quantifier
def is_quantifier(string: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return string == "A" or string == "E"


@frozen
class Formula:
    """An immutable predicate-logic formula in tree representation, composed
    from relation names applied to predicate-logic terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments of the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        statement (`~typing.Optional`\\[`Formula`]): the statement quantified by
            the root, if the root is a quantification.
    """

    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    statement: Optional[Formula]

    def __init__(
        self,
        root: str,
        arguments_or_first_or_variable: Union[Sequence[Term], Formula, str],
        second_or_statement: Optional[Formula] = None,
    ):
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable name and statement.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments for the root, if the
                root is a relation name or the equality relation; the first
                operand for the root, if the root is a unary or binary operator;
                the variable name to be quantified by the root, if the root is a
                quantification.
            second_or_statement: the second operand for the root, if the root is
                a binary operator; the statement to be quantified by the root,
                if the root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert isinstance(
                arguments_or_first_or_variable, Sequence
            ) and not isinstance(arguments_or_first_or_variable, str)
            if is_equality(root):
                assert len(arguments_or_first_or_variable) == 2
            assert second_or_statement is None
            self.root, self.arguments = root, tuple(
                arguments_or_first_or_variable
            )
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula)
            assert second_or_statement is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula)
            assert second_or_statement is not None
            self.root, self.first, self.second = (
                root,
                arguments_or_first_or_variable,
                second_or_statement,
            )
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.statement
            assert isinstance(
                arguments_or_first_or_variable, str
            ) and is_variable(arguments_or_first_or_variable)
            assert second_or_statement is not None
            self.root, self.variable, self.statement = (
                root,
                arguments_or_first_or_variable,
                second_or_statement,
            )

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 7.2
        if is_equality(self.root):
            assert len(self.arguments) == 2  # type: ignore
            return f"{str(self.arguments[0])}={str(self.arguments[1])}"  # type: ignore
        if is_unary(self.root):
            assert self.first
            return f"~{str(self.first)}"
        if is_relation(self.root):
            assert self.arguments is not None
            args: Sequence[str] = [str(arg) for arg in self.arguments]
            return f"{self.root}({','.join(args)})"
        if is_binary(self.root):
            assert self.first and self.second
            return f"({str(self.first)}{self.root}{str(self.second)})"
        if is_quantifier(self.root):
            assert self.variable and self.statement
            return f"{self.root}{self.variable}[{str(self.statement)}]"

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'f(y)=c12'``) or by a variable
            name (e.g., ``'f(y)=x12'``), then the parsed prefix will include
            that entire name (and not just a part of it, such as ``'f(y)=x1'``).
        """
        # Task 7.4a
        return FormulaParser().parse(string)

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        # Task 7.4b
        return Formula._parse_prefix(string)[0]

    # TODO - Refactor all Task 7.6's funcs (Yikes!)

    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """
        # Task 7.6a

        if is_equality(self.root) or is_relation(self.root):
            assert self.arguments
            return set(
                it_chain.from_iterable(
                    arg.constants() for arg in self.arguments
                )
            )

        if is_quantifier(self.root):
            assert self.statement
            return self.statement.constants()

        if is_unary(self.root):
            assert self.first
            return self.first.constants()

        if is_binary(self.root):
            assert self.first and self.second
            return self.first.constants() | self.second.constants()

    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 7.6b

        if is_equality(self.root) or is_relation(self.root):
            assert self.arguments
            return set(
                it_chain.from_iterable(
                    arg.variables() for arg in self.arguments
                )
            )

        if is_quantifier(self.root):
            assert self.statement and self.variable
            return self.statement.variables() | {self.variable}

        if is_unary(self.root):
            assert self.first
            return self.first.variables()

        if is_binary(self.root):
            assert self.first and self.second
            return self.first.variables() | self.second.variables()

    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of every variable name that is used in te hcurrent formula not
            only within a scope of a quantification on that variable name.
        """
        # Task 7.6c

        if is_equality(self.root) or is_relation(self.root):
            # assert self.arguments
            return set(
                it_chain.from_iterable(
                    arg.variables() for arg in self.arguments
                )
            )

        if is_quantifier(self.root):
            assert self.statement
            return self.statement.free_variables() - {self.variable}

        if is_unary(self.root):
            assert self.first
            return self.first.free_variables()

        if is_binary(self.root):
            assert self.first and self.second
            return self.first.free_variables() | self.second.free_variables()

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        # Task 7.6d

        if is_equality(self.root) or is_relation(self.root):
            return set(
                it_chain.from_iterable(
                    arg.functions() for arg in self.arguments
                )
            )

        if is_quantifier(self.root):
            assert self.statement
            return self.statement.functions()

        if is_unary(self.root):
            assert self.first
            return self.first.functions()

        if is_binary(self.root):
            assert self.first and self.second
            return self.first.functions() | self.second.functions()

    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        # Task 7.6e

        if is_equality(self.root):
            return set()

        if is_relation(self.root):
            return {(self.root, len(self.arguments))}

        if is_quantifier(self.root):
            assert self.statement
            return self.statement.relations()

        if is_unary(self.root):
            assert self.first
            return self.first.relations()

        if is_binary(self.root):
            assert self.first and self.second
            return self.first.relations() | self.second.relations()

    def substitute(
        self,
        substitution_map: Mapping[str, Term],
        forbidden_variables: AbstractSet[str] = frozenset(),
    ) -> Formula:
        """Substitutes in the current formula, each constant name `construct` or
        free occurrence of variable name `construct` that is a key in
        `substitution_map` with the term
        `substitution_map`\ ``[``\ `construct`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variable names not allowed in substitution
                terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant name and variable name occurrences originating in the
            current formula are substituted (i.e., those originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable name from `forbidden_variables`
                or a variable name occurrence that becomes bound when that term
                is substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for construct in substitution_map:
            assert is_constant(construct) or is_variable(construct)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.2

        if is_equality(self.root) or is_relation(self.root):
            args: List[Term] = [
                arg.substitute(substitution_map, forbidden_variables)
                for arg in self.arguments
            ]

            return Formula(self.root, args)

        elif is_unary(self.root):
            assert self.first

            return Formula(
                self.root,
                self.first.substitute(substitution_map, forbidden_variables),
            )

        elif is_binary(self.root):
            assert self.first and self.second

            return Formula(
                self.root,
                self.first.substitute(substitution_map, forbidden_variables),
                self.second.substitute(substitution_map, forbidden_variables),
            )

        elif is_quantifier(self.root):
            assert self.variable and self.statement

            return Formula(
                self.root,
                self.variable,
                self.statement.substitute(
                    {
                        k: v
                        for k, v in substitution_map.items()
                        if k != self.variable
                    },
                    set(forbidden_variables).union({self.variable}),
                ),
            )

        return self.substitute(substitution_map, forbidden_variables)

    def propositional_skeleton(
        self,
    ) -> Tuple[PropositionalFormula, Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation name or quantifier at its root with a
            propositional variable name, consistently such that multiple
            identical such (outermost) subformulas are substituted with the same
            propositional variable name. The propositional variable names used
            for substitution are obtained, from left to right (considering their
            first occurrence), by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a mapping from each propositional
            variable name to the subformula for which it was substituted.

        Examples:
            >>> formula = Formula.parse('((Ax[x=7]&x=7)|(~Q(y)->x=7))')
            >>> formula.propositional_skeleton()
            (((z1&z2)|(~z3->z2)), {'z1': Ax[x=7], 'z2': x=7, 'z3': Q(y)})
            >>> formula.propositional_skeleton()
            (((z4&z5)|(~z6->z5)), {'z4': Ax[x=7], 'z5': x=7, 'z6': Q(y)})
        """

        prop_form_to_pred_form: Dict[Formula, str] = dict()

        def _helper(formula: Formula) -> PropositionalFormula:
            if is_unary(formula.root):
                return PropositionalFormula(
                    formula.root, _helper(formula.first)
                )

            if is_binary(formula.root):
                return PropositionalFormula(
                    formula.root,
                    _helper(formula.first),
                    _helper(formula.second),
                )
            else:
                if formula in prop_form_to_pred_form.keys():
                    return PropositionalFormula(prop_form_to_pred_form[formula])
                else:
                    prop_form: str = next(fresh_variable_name_generator)
                    prop_form_to_pred_form[formula] = prop_form
                    return PropositionalFormula(prop_form)

        formula_as_prop_formula = _helper(self)

        return formula_as_prop_formula, {
            v: k for k, v in prop_form_to_pred_form.items()
        }

    @staticmethod
    def from_propositional_skeleton(
        skeleton: PropositionalFormula, substitution_map: Mapping[str, Formula]
    ) -> Formula:
        """Computes a predicate-logic formula from a propositional skeleton and
        a substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute,
                containing no constants or operators beyond ``'~'``, ``'->'``,
                ``'|'``, and ``'&'``.
            substitution_map: mapping from each propositional variable name of
                the given propositional skeleton to a predicate-logic formula.

        Returns:
            A predicate-logic formula obtained from the given propositional
            skeleton by substituting each propositional variable name with the
            formula mapped to it by the given map.

        Examples:
            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z1&z2)|(~z3->z2))'),
            ...     {'z1': Formula.parse('Ax[x=7]'), 'z2': Formula.parse('x=7'),
            ...      'z3': Formula.parse('Q(y)')})
            ((Ax[x=7]&x=7)|(~Q(y)->x=7))

            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z9&z2)|(~z3->z2))'),
            ...     {'z2': Formula.parse('x=7'), 'z3': Formula.parse('Q(y)'),
            ...      'z9': Formula.parse('Ax[x=7]')})
            ((Ax[x=7]&x=7)|(~Q(y)->x=7))
        """
        for operator in skeleton.operators():
            assert is_unary(operator) or is_binary(operator)
        for variable in skeleton.variables():
            assert variable in substitution_map
        # Task 9.10

        if is_unary(skeleton.root):
            return Formula(
                skeleton.root,
                Formula.from_propositional_skeleton(
                    skeleton.first, substitution_map
                ),
            )

        if is_binary(skeleton.root):
            return Formula(
                skeleton.root,
                Formula.from_propositional_skeleton(
                    skeleton.first, substitution_map
                ),
                Formula.from_propositional_skeleton(
                    skeleton.second, substitution_map
                ),
            )

        return substitution_map[skeleton.root]
