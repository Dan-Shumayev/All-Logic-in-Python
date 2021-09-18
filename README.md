## **Logic projects will be accordingly tagged, shared and managed via this repository**

#### The first half of the course deals with propositional logic, in particular:
- We formally define grammar rules for describing a propositional formula of this type.
    - We'll look at some equivalent ways to describe such formulas:
        * A string of characters
        * A tree-like structure
        * A data structure implemented in Python

<details>
<summary><code>Chapter 1</code> - <b>Syntax</b></summary>

- `Propositional Formula` - defined recursively by the atomic propositions represented by `p` to `z` (possibly followed by any amount of digits), `T`, `F`, such that if `φ` and `ψ` are valid propositional formulas then so are:

    - (`φ | ψ`)
    - (`φ -> ψ`)
    - (`φ & ψ`)
    - `~φ`

    **Note:** The existence or non-existence of parentheses is obligatory.

- `Recursive-Descent Parsing` - a way to parse various context-free languages including ours in this course. The idea behind this parser is that it dictates the suitable unique way of reading the rest of the formula according to the current token (`T`, `F`, `(`, `)`, `~`, `&`, `|`, `p`, `q76`).
    - In general, given this formula:
        - `(φ • ψ)`
    - We recursively read it this way: upon encountering the open parenthesis `(`, we know this would be followed by formula `φ` (**the recursive aspect**), binary operator `•`, formula `ψ`, closing parenthesis `)`.
    - In order for us to create a recursive descent parser, we first have to describe our logic's grammar. We'll define our syntax using a context-free grammar:
        ```
        Formula ::= (Formula BinaryOp Formula) | UnaryOp Formula | Constant | Var   ---   **Lowest precedence**
        BinaryOp ::= (Formula&Formula) | (Formula&Formula) | (Formula->Formula)
        UnaryOp ::= ~Var | ~Constant | ~Formula
        Constant ::= T | F
        Var ::= [p-z]+[0-9]*   ---   **Highest precedence**
        ```
    **Note:** In my RD-parser I didn't use a `lexer` (as a separate entity) in order to classify the tokens and iterating over them. There would be at least 2 advantages of doing that:

    - A `lexer` separates the input into tokens which carry additional information: the token type and the exact position of the token in the input string. We can use this position information to generate detailed error messages. This is time saved for the future users of the parser.
    - We could use Python's own `lexer` and filter the stream of tokens, thus using an extremely robust `lexer` (`tokenizer.tokenize` and `io.BytesIO`).</details>

<details>
<summary><code>Chapter 2</code> - <b>Semantics</b></summary>

- `Model` - We define it as a function taking a set of atomic propositions to {True, False} (aka `T` and `F` in our syntax). Put simply, it's a set of propositions.
    - The **value of a proposition** in a Model is defined recursively:
        - **Base case** - `T`, `F` gets the value of `True` and `False` respectively.
        - **The recursion step** - inspect the type of the token we're dealing with such that:
            - If `φ` is a variable, we apply the Model function (`M`) on it, resulting in its value.
            - If `φ=~ψ`, then `φ` is `True` iff `M(ψ)` is `False`(which is in its turn determined by the former case).
            - If `(φ = ε • ψ)`, then `φ`'s value is `True` iff the value of (either/both - `|`/`&` respectively) `ε` or/and (respectively) `ψ` is `True` in `M`.
            - If `(φ = ψ -> ε)`, then `φ`'s value is `True` if either `φ` (in `M`) `False` or if the value of `ε` (in `M`) is `True`.
    - `Tautology` - A formula that in every model evaluates to `True` (The rightmost column in its truth table is `True`).
    - `Contradiction` - The negation of a tautology. That is, a formula that evaluates to `False` in every model (The rightmost column in its truth table is `False`).
    - `Satisfiability` - A formula that evaluates to `True` in some model (The rightmost column in its truth table contains a cell of `True`). That is, a satisfiable formula is not a contradiction.
- `DNF`/`CNF` - Ways to express a proposition out of its truth table (Discrete Math). Using a `DNF` we look at the `True` values for the formula, "forcing" its respective model to evaluate to `True` upon `&`'ing its variables, then `|`ing all these models, resulting in a possible proposition representing the formula.
- `NP` and `Reduction` - Every `NP` problem is reducible to `SAT` (which is `NP-Complete` as you may recall). In particular, the `3-Coloring` problem is reducible to `SAT` using the vertices as the proposition's literals.</details>

<details>
<summary><code>Chapter 3</code> - <b>Formula subtitutions/Sets of operators</b></summary>

- More operators - `XOR`, `Iff`, `Nand`, `Nor` (have been taught in `Nand2Tetris`).
    - **Note** - We're able to express any operator using either `Nor` or `Nand` (aka universal functions). Also, note that it's critic for computer architectures' considerations as it may allow them to product minimum amount of chips -> cheaper.
- `Subtitutions` - Converting formulas that use one set of operators to using another set of operators.
</details>