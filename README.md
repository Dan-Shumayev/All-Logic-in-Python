## **Logic projects will be accordingly tagged, shared and managed via this repository**

#### The first half of the course deals with propositional logic, in particular:
- We formally define grammar rules for describing a propositional formula of this type.
    - We'll look at some equivalent ways to describe such formulas:
        * A string of characters
        * A tree-like structure
        * A data structure implemented in Python


#### - `Chapter 1` -
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