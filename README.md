## **Logic projects will be accordingly tagged, shared and managed via this repository**

#### The first half of the course deals with propositional logic, in particular:
- We formally define grammar rules for describing a propositional formula of this type.
    - We'll look at some equivalent ways to describe such formulas:
        * A string of characters
        * A tree-like structure
        * A data structure implemented in Python


#### - `Chapter 1` -
    - `Propositional Formula` - defined recursively by the atomic propositions represented by `p` to `z`, `T`, `F`, such that if `φ` and `ψ` are valid propositional formulas then so are:
        - (`φ | ψ`)
        - (`φ -> ψ`)
        - (`φ & ψ`)
        - (`~φ`)