# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/syntax.py


"""Syntactic handling of propositional formulas."""

# needed to be able to reference types before they're defined (forward declaration)
from __future__ import annotations, generator_stop

from functools import lru_cache  # cache last `maxsize` calls to the decorated func
from re import compile as regex_compile
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method

# constants:
OPEN_BINARY_FORM: str = "("
CLOSE_BINARY_FORM: str = ")"


###### RD Parser ######
# A simple RD parser for the following grammar:
#
# Formula ::= (Formula BinaryOp Formula) | ~Formula | Var ---**Lowest precedence**
# BinaryOp ::= (Formula&Formula) | (Formula|Formula) | (Formula->Formula)
# UnaryOp ::= ~Var | ~Formula
# Var ::= [p-z]   ---   **Highest precedence**


##### Regexes to match the respective tokens #####
BINARY_OP_RE = regex_compile(r"&|->|\|")
UNARY_OP_RE = regex_compile(r"~")
CONSTANT_RE = regex_compile(r"T|F")
VARIABLE_RE = regex_compile(r"[p-z]+\d*")

######## Start of my trial to implement a firmer hierarchy as befits a RD parser ########
# class TokenType(str, Enum):
#     And: str = "&"
#     Or: str = "|"
#     Imply: str = "->"
#     Neg: str = "~"
#     T: str = "T"
#     F: str = "F"


##### Token types: #####
# BinaryOp = Union[TokenType.And, TokenType.Or, TokenType.Imply]
# UnaryOp = Union[TokenType.Neg]

#### Tokens: ####
# Variable = str

# Constant = Union[TokenType.T, TokenType.F]

# @dataclass
# class UnaryFormula:
#     op: UnaryOp
#     operand: Optional[Formula]  # To follow the typing of Formula class,
#     # though it doesn't make sense for this field to be None

# @dataclass
# class BinaryFormula:
#     left: Optional[Formula]
#     right: Optional[Formula]
#     op: BinaryOp

# ParserFormula = Union[Variable, Constant, UnaryFormula, BinaryFormula]

# def parser_adapter_to_formula(formula_to_adapt: ParserFormula) -> Optional[Formula]:
#     if isinstance(formula_to_adapt, Variable):
#         return Formula(formula_to_adapt, None, None)
#     if isinstance(formula_to_adapt, UnaryFormula):
#         return Formula(formula_to_adapt.op, formula_to_adapt.operand, None)
#     if isinstance(formula_to_adapt, BinaryFormula):
#         return Formula(
#             formula_to_adapt.op, formula_to_adapt.left, formula_to_adapt.right
#         )
#     return None

######## End of trial to implement a firmer hierarchy ########

# each parser will return the parsed element, tupled with
# the remainder of the parsing


def parse_formula(string_to_parse: str) -> FormulaPrefix:
    """Parses a string to its respective Formula object, tupled with its remainder
    which isn't derived by our logic's grammar.

    Parameters:
        formula_to_parse: The string to parse.

    Returns:
        A tuple of Formula object with its string remainder if exists (None if not).
    """
    if string_to_parse.startswith(OPEN_BINARY_FORM):
        # BinaryOp -> Lowest precedence -> Rooted as ancestor of other operations
        # that have higher precdence (UnaryOp/Var)
        return parse_binary_formula(string_to_parse)
        # binary_formula, remainder = parse_binary_formula(string_to_parse)
        # return parser_adapter_to_formula(binary_formula), remainder
    elif UNARY_OP_RE.match(string_to_parse):
        return parse_unary_formula(string_to_parse)
        # unary_formula, remainder = parse_unary_formula(string_to_parse)
        # return parser_adapter_to_formula(unary_formula), remainder
    elif VARIABLE_RE.match(string_to_parse) or CONSTANT_RE.match(string_to_parse):
        return parse_variable_constant(string_to_parse)
        # var_or_const, remainder = parse_variable_constant(string_to_parse)
        # return (
        #     parser_adapter_to_formula(var_or_const),
        #     remainder,
        # )
    else:
        return None, string_to_parse


def parse_binary_formula(string_to_parse: str) -> FormulaPrefix:
    """Parses a string to its respective tree-like structure that is compatible
    with a binary operator grammar rules. The binray operator is the father of
    the left-hand side Formula (the left child) and the right-hand side Formula
    (the right child).

    Parameters:
        formula_to_parse: The string to parse.

    Returns:
        A tuple of the BinaryFormula prefix and its remainder string.
    """
    assert string_to_parse.startswith(
        OPEN_BINARY_FORM
    ), "Expected binary formula to begin with '('"

    left, left_remainder = parse_formula(string_to_parse[1:])

    match = BINARY_OP_RE.match(left_remainder)
    if not match:
        return (
            None,
            "Expected the remainder of the lefthand side of the binary formula "
            "to begin with a binary operator",
        )

    op: str = match.group(0)
    # MatchObject.end(0) will return the index of the
    # first character that wasn't matched by the regex, which should
    # be the first letter after the operator.
    op_remainder: str = left_remainder[match.end(0) :]
    assert op_remainder, "The remainder of the binary operator should be non empty"

    right, right_remainder = parse_formula(op_remainder)
    if not right_remainder.startswith(CLOSE_BINARY_FORM):
        return (
            None,
            "The remainder of the righthand side of "
            "the binary formula should start with ')''",
        )

    return Formula(op, left, right), right_remainder[1:]
    # return BinaryFormula(left=left, right=right, op=op), right_remainder[1:]


def parse_unary_formula(string_to_parse: str) -> FormulaPrefix:
    """

    Parameters:
        string_to_parse: The string to parse.

    Returns:
        A tuple of the UnaryFormula prefix and its remainder string.
    """
    match = UNARY_OP_RE.match(string_to_parse)
    assert match, "Expected to start with a unary operator"
    op: str = match.group(0)
    op_remainder: str = string_to_parse[match.end(0) :]

    operand, remainder = parse_formula(op_remainder)
    return (Formula(op, operand, None), remainder) if operand else (None, op)
    # return UnaryFormula(op=op, operand=operand), remainder


def parse_variable_constant(
    string_to_parse: str,
) -> FormulaPrefix:
    """

    Parameters:
        string_to_parse: The string to parse.

    Returns:

    """
    match_var = VARIABLE_RE.match(string_to_parse)
    if match_var:
        return match_string_and_remainder(match_var, string_to_parse)

    match_const = CONSTANT_RE.match(string_to_parse)
    assert match_const, "Expected to start with variable or constant"
    return match_string_and_remainder(match_const, string_to_parse)


def match_string_and_remainder(match_token, string_to_parse):
    root: str = match_token.group(0)
    remainder: str = string_to_parse[match_token.end(0) :]
    return Formula(root, None, None), remainder


###### End of RD Parser ######


@lru_cache(maxsize=100)  # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is an atomic proposition.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is an atomic proposition, ``False``
        otherwise.
    """
    return (
        string[0] >= "p"
        and string[0] <= "z"
        and (len(string) == 1 or string[1:].isdigit())
    )


@lru_cache(maxsize=100)  # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return string == "T" or string == "F"


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
    # For Chapter 3:
    # return string in {'&', '|',  '->', '+', '<->', '-&', '-|'}


@frozen
class Formula:
    """An immutable propositional formula in tree representation, composed from
    atomic propositions, and operators applied to them.

    Attributes:
        root (`str`): the constant, atomic proposition, or operator at the root
            of the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand to the
            root, if the root is a binary operator.
    """

    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(
        self,
        root: str,
        first: Optional[Formula] = None,
        second: Optional[Formula] = None,
    ):
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand to the root, if the root is a unary or
                binary operator.
            second: the second operand to the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert first is not None and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root)
            assert first is not None and second is not None
            self.root, self.first, self.second = root, first, second

    @staticmethod
    def negate_formula(formula: Formula) -> str:
        """Negates a formula.

        Parameters:
            formula: A formula to negate.

        Returns:
            A string reresenting the formula negated.
        """
        return formula.root + Formula.formula_obj_to_string(formula.first)  # type: ignore

    @staticmethod
    def create_binary_formula(
        binary_operator: str, first_sub_formula: Formula, second_sub_formula: Formula
    ) -> str:
        """Assmebles a binary formula out of two sub-formulas.

        Parameters:
            binary_operator: The binary operator applied on the two sub-formulas.
            first_sub_formula: The first sub-formula.
            second_sub_formula: The second sub-formula.

        Returns:
            A string reresenting the suitable binary formula.
        """
        return (
            OPEN_BINARY_FORM
            + Formula.formula_obj_to_string(first_sub_formula)
            + binary_operator
            + Formula.formula_obj_to_string(second_sub_formula)
            + CLOSE_BINARY_FORM
        )

    @staticmethod
    def formula_obj_to_string(formula: Formula) -> str:
        """Recursive function to assemble a string representation of the formula described by the
        Formula object.

        Parameters:
            formula: The Formula object to build the string repr. of.

        Returns:
            A string representing the formula object.
        """
        if is_variable(formula.root) or is_constant(formula.root):
            return formula.root
        return (
            Formula.negate_formula(formula)
            if is_unary(formula.root)
            else Formula.create_binary_formula(
                formula.root, formula.first, formula.second  # type: ignore
            )
        )

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 1.1
        return Formula.formula_obj_to_string(self)

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
    def extract_variables_from_formula(
        formula: Formula, res: Set[str] = set()
    ) -> Set[str]:
        """

        Parameters:
            formula:
            res:

        Returns:

        """
        if is_variable(formula.root):
            return res | {formula.root}
        elif is_constant(formula.root):
            return res  # Nothing to append - 'T'/'F' are not variables
        return (
            Formula.extract_variables_from_formula(formula.first, res)  # type: ignore
            if is_unary(formula.root)
            # Binary case:
            else Formula.extract_variables_from_formula(formula.first, res)  # type: ignore
            | Formula.extract_variables_from_formula(formula.second, res)  # type: ignore
        )

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """

        Returns:

        """
        """Finds all atomic propositions (variables) in the current formula.

        Returns:
            A set of all atomic propositions used in the current formula.
        """
        # Task 1.2
        return Formula.extract_variables_from_formula(self)

    @staticmethod
    def extract_operators_from_formula(
        formula: Formula, res: Set[str] = set()
    ) -> Set[str]:
        """

        Parameters:
            formula:
            res:

        Returns:

        """
        if is_constant(formula.root):
            return res | {formula.root}
        elif is_variable(formula.root):
            return res  # Nothing to append - p..z possibly followed be digits are not operators
        return (
            # Unary case: '~' is possibly followed by 'T'/'F' operators
            {"~"} | Formula.extract_operators_from_formula(formula.first)  # type: ignore
            if is_unary(formula.root)
            # Binary case (append the binary operator):
            else Formula.extract_operators_from_formula(formula.first, res)  # type: ignore
            | Formula.extract_operators_from_formula(formula.second, res)  # type: ignore
            | {formula.root}
        )

    @memoized_parameterless_method
    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3
        return Formula.extract_operators_from_formula(self)

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a variable name (e.g.,
            ``'x12'``) or a unary operator follows by a variable name, then the
            parsed prefix will include that entire variable name (and not just a
            part of it, such as ``'x1'``). If no prefix of the given string is a
            valid standard string representation of a formula then returned pair
            should be of ``None`` and an error message, where the error message
            is a string with some human-readable content.
        """
        # Task 1.4
        return parse_formula(string)

    @staticmethod
    def is_formula(string: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            string: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # Task 1.5

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(string)
        # Task 1.6

    # Optional tasks for Chapter 1

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

    @staticmethod
    def parse_polish(string: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

    def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each variable `v` that is a key
        in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            variables originating in the current formula are substituted (i.e.,
            variables originating in one of the specified substitutions are not
            subjected to additional substitutions).

        Examples:
            >>> Formula.parse('((p->p)|r)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)'), 'r': Formula.parse('p')})
            (((q&r)->(q&r))|p)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3

    def substitute_operators(self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            operators originating in the current formula are substituted (i.e.,
            operators originating in one of the specified substitutions are not
            subjected to additional substitutions).

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_binary(operator) or is_unary(operator) or is_constant(operator)
            assert substitution_map[operator].variables().issubset({"p", "q"})
        # Task 3.4


FormulaPrefix = Tuple[
    Optional[Formula], str
]  # TODO - move it to above - forward declare Formula
