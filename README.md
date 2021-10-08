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
- `Complete set of oprerators` - A set of operators from which any other boolean function can be derived (that is, the same truth table).
    - For example, the set of operators `{&, |, ~}` is complete as we've proved in (chpater02, task-2.7).
        - **Conclusion** - Any set of operators that is able to derive these three operators is also complete (`Nand`, `Nor`).
    - **Ways of proving incompleteness of operator sets**:
        - **Incompleteness proof** - Showing that every boolean function over the said set of operators is preserving some property denoted by `P` (usually done by induction). Hence, we show that there is an operator that does not hold the `P`-preserveness (so the first set lacks at least one operator `->` isn't complete).
        - **Another way to refute set-completeness** - Showing that every boolean function using only the said set of operators is affine by showing that every subset of the operators is equivalent to `XOR` and `~`. Now, we know that the operator `&` is not affine, thus the affine set is not complete.
            - **Note:** - Each operator is affine if there exists an isomorphic matrix of the form Ax + b (in particular, any linear transformation is affine). Note that `<->` is affine as it can be expressed as a composition of affines (`Negation` of `XOR` which are both linear transformations.)
        - **Another way to refute set-completeness** - Showing that every boolean function using the said set of operators is *monotone* (Changing an input from `F` to `T` never changes the output from `T` to `F`). `~` is not monotone. hence is not in the set, and the set is incomplete.
</details>

<details>
<summary><code>Chapter 4</code> - <b>Deductive Proofs</b></summary>

- **Anatomy of a deductive proof** - Using syntactic inference rules `R` and a set of given assumptions, we infer conclusions out of the previous rules and conclusions.
    - *Inference rule* - List (of a non-negative length) consiting of formulas (i.e. represented by the `Formula` object) that function as assumptions, and a formula that is their conclusion.
    - *Soundness* - We say that a set `A` of formulas **entails** a formula `ψ` if every model that satisfies all the assumptions in `A` also satisfies `ψ`. We denote *A entails `ψ`* by `A ⊨ ψ`.
        - It may be also *trivially* sound, when there is no model that satisfies the set of assumptions at all (`A`).
    - *Specialization* - We may refer to inference rules as templates where their variable names serve as placeholders for any kind of formulas.
    - **The Soundness Theorem** (The glue between the syntactic and semantic proofs) - An inference rule is *sound* if its assumptions *entail* (every model satisying the assumptions so satifies the conclusion) its conclusion.
    - **The theorem** - An inference rule that is proven only using sound inference rules, is itself sound. Actually, it promises us that everything we have done so far (syntactic proofs) is not redundant, but does proves a conclusion is true.
        - *Sketch of Proof* - Assume by the way of contradiction that all the inference rules (previous lines in proof) are sound but there is a model that does not satisfy the required conclusion (i.e. the conclusion isn't sound). Hence, it implies that there is at least one previous line that is not sound, in contradiction to the assumption.
        - *Semantics of Specializaiton*  - A specialization of a sound inference rule (and for a proof of a sound inference rule) is itself sound. The proof goes the same (*I have discovered a truly marvelous proof of this, which this margin is too narrow to contain*).
</details>

<details>
<summary><code>Chapter 5</code> - <b>Deductive proofs - continued</b></summary>

- **Deduction Theorem** -
    - *Modus Ponens* - Given that `p` and `p->q` hold, we can deduce `q`.
        - First direction - We can use *MP* in order to turn axiomatic-like inference rules (`{} ⊨ φ->ψ`) to a regular proof (`{φ}->ψ`) using only the *Modus Ponens* rule. 
        - Second direction - if `{φ}->ψ` then `{} ⊨ φ->ψ`. More generally, for any set of additional assumptions `A`, if `A∪{φ} ⊨ ψ` then `A ⊨ φ->ψ`.
</details>