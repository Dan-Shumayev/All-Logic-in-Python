# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2021
# File name: predicates/some_proofs.py

"""Some proofs in Predicate Logic."""

from predicates.deduction import *
from predicates.prenex import equivalence_of
from predicates.proofs import *
from predicates.prover import *
from predicates.syntax import *


def prove_syllogism(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[(Man(x)->Mortal(x))]", "Man(aristotle)"}, print_as_proof_forms
    )
    step1 = prover.add_assumption("Ax[(Man(x)->Mortal(x))]")
    step2 = prover.add_instantiated_assumption(
        "(Ax[(Man(x)->Mortal(x))]->(Man(aristotle)->Mortal(aristotle)))",
        Prover.UI,
        {"R": "(Man(_)->Mortal(_))", "c": "aristotle"},
    )
    step3 = prover.add_mp("(Man(aristotle)->Mortal(aristotle))", step1, step2)
    step4 = prover.add_assumption("Man(aristotle)")
    step5 = prover.add_mp("Mortal(aristotle)", step4, step3)
    return prover.qed()


def prove_syllogism_with_universal_instantiation(
    print_as_proof_forms: bool = False,
) -> Proof:
    """Using the method `~predicates.prover.Prover.add_universal_instantiation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof, created with the help of the method
        `~predicates.prover.Prover.add_universal_instantiation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[(Man(x)->Mortal(x))]", "Man(aristotle)"}, print_as_proof_forms
    )
    step1 = prover.add_assumption("Ax[(Man(x)->Mortal(x))]")
    step2 = prover.add_universal_instantiation(
        "(Man(aristotle)->Mortal(aristotle))", step1, "aristotle"
    )
    step3 = prover.add_assumption("Man(aristotle)")
    step4 = prover.add_mp("Mortal(aristotle)", step3, step2)
    return prover.qed()


def prove_syllogism_all_all(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[(Greek(x)->Human(x))]", "Ax[(Human(x)->Mortal(x))]"},
        print_as_proof_forms,
    )
    step1 = prover.add_assumption("Ax[(Greek(x)->Human(x))]")
    step2 = prover.add_universal_instantiation(
        "(Greek(x)->Human(x))", step1, "x"
    )
    step3 = prover.add_assumption("Ax[(Human(x)->Mortal(x))]")
    step4 = prover.add_universal_instantiation(
        "(Human(x)->Mortal(x))", step3, "x"
    )
    step5 = prover.add_tautology(
        "((Greek(x)->Human(x))->((Human(x)->Mortal(x))->(Greek(x)->Mortal(x))))"
    )
    step6 = prover.add_mp(
        "((Human(x)->Mortal(x))->(Greek(x)->Mortal(x)))", step2, step5
    )
    step7 = prover.add_mp("(Greek(x)->Mortal(x))", step4, step6)
    step8 = prover.add_ug("Ax[(Greek(x)->Mortal(x))]", step7)
    return prover.qed()


def prove_syllogism_all_all_with_tautological_implication(
    print_as_proof_forms: bool = False,
) -> Proof:
    """Using the method
    `~predicates.prover.Prover.add_tautological_implication`, proves from the
    assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof, created with the help of the method
        `~predicates.prover.Prover.add_tautological_implication`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[(Greek(x)->Human(x))]", "Ax[(Human(x)->Mortal(x))]"},
        print_as_proof_forms,
    )
    step1 = prover.add_assumption("Ax[(Greek(x)->Human(x))]")
    step2 = prover.add_universal_instantiation(
        "(Greek(x)->Human(x))", step1, "x"
    )
    step3 = prover.add_assumption("Ax[(Human(x)->Mortal(x))]")
    step4 = prover.add_universal_instantiation(
        "(Human(x)->Mortal(x))", step3, "x"
    )
    # step1 = prover.add_assumption("Ax[(Human(x)->Mortal(x))]")
    # step2 = prover.add_universal_instantiation(
    #     "(Human(x)->Mortal(x))", step1, "x"
    # )
    # step3 = prover.add_assumption("Ax[(Greek(x)->Human(x))]")
    # step4 = prover.add_universal_instantiation(
    #     "(Greek(x)->Human(x))", step3, "x"
    # )
    step5 = prover.add_tautological_implication(
        "(Greek(x)->Mortal(x))", {step2, step4}
    )
    step6 = prover.add_ug("Ax[(Greek(x)->Mortal(x))]", step5)
    return prover.qed()


def prove_syllogism_all_exists(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)

    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[(Man(x)->Mortal(x))]", "Ex[Man(x)]"}, print_as_proof_forms
    )
    step1 = prover.add_assumption("Ax[(Man(x)->Mortal(x))]")
    step2 = prover.add_assumption("Ex[Man(x)]")
    step3 = prover.add_universal_instantiation(
        "(Man(x)->Mortal(x))", step1, "x"
    )
    step4 = prover.add_instantiated_assumption(
        "(Mortal(x)->Ex[Mortal(x)])", Prover.EI, {"R": "Mortal(_)", "c": "x"}
    )
    step5 = prover.add_tautological_implication(
        "(Man(x)->Ex[Mortal(x)])", {step3, step4}
    )
    step6 = prover.add_ug("Ax[(Man(x)->Ex[Mortal(x)])]", step5)
    step7 = prover.add_instantiated_assumption(
        "((Ax[(Man(x)->Ex[Mortal(x)])]&Ex[Man(x)])->Ex[Mortal(x)])",
        Prover.ES,
        {"R": "Man(_)", "Q": "Ex[Mortal(x)]"},
    )
    step8 = prover.add_tautological_implication(
        "Ex[Mortal(x)]", {step2, step6, step7}
    )
    return prover.qed()


def prove_syllogism_all_exists_with_existential_derivation(
    print_as_proof_forms: bool = False,
) -> Proof:
    """Using the method `~predicates.prover.Prover.add_existential_derivation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)

    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof, created with the help of the method
        `~predicates.prover.Prover.add_existential_derivation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[(Man(x)->Mortal(x))]", "Ex[Man(x)]"}, print_as_proof_forms
    )
    step1 = prover.add_assumption("Ax[(Man(x)->Mortal(x))]")
    step2 = prover.add_assumption("Ex[Man(x)]")
    step3 = prover.add_universal_instantiation(
        "(Man(x)->Mortal(x))", step1, "x"
    )
    step4 = prover.add_instantiated_assumption(
        "(Mortal(x)->Ex[Mortal(x)])", Prover.EI, {"R": "Mortal(_)", "c": "x"}
    )
    step5 = prover.add_tautological_implication(
        "(Man(x)->Ex[Mortal(x)])", {step3, step4}
    )
    step6 = prover.add_existential_derivation("Ex[Mortal(x)]", step2, step5)
    return prover.qed()


def prove_lovers(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. Everybody loves somebody (``'Ax[Ey[Loves(x,y)]]'``), and
    2. Everybody loves a lover (``'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'``)

    the conclusion: Everybody loves everybody (``'Ax[Az[Loves(z,x)]]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[Ey[Loves(x,y)]]", "Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]"},
        print_as_proof_forms,
    )
    # Task 10.4

    step1 = prover.add_assumption("Ax[Ey[Loves(x,y)]]")
    step2 = prover.add_universal_instantiation("Ey[Loves(x,y)]", step1, "x")
    step3 = prover.add_assumption("Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]")
    step4 = prover.add_universal_instantiation(
        "Az[Ay[(Loves(x,y)->Loves(z,x))]]", step3, "x"
    )
    step5 = prover.add_universal_instantiation(
        "Ay[(Loves(x,y)->Loves(z,x))]", step4, "z"
    )
    step6 = prover.add_universal_instantiation(
        "(Loves(x,y)->Loves(z,x))", step5, "y"
    )
    step7 = prover.add_existential_derivation("Loves(z,x)", step2, step6)
    step8 = prover.add_ug("Az[Loves(z,x)]", step7)

    prover.add_ug("Ax[Az[Loves(z,x)]]", step8)

    return prover.qed()


def prove_homework(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. No homework is fun (``'~Ex[(Homework(x)&Fun(x))]'``), and
    2. Some reading is homework (``'Ex[(Homework(x)&Reading(x))]'``)

    the conclusion: Some reading is not fun (``'Ex[(Reading(x)&~Fun(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"~Ex[(Homework(x)&Fun(x))]", "Ex[(Homework(x)&Reading(x))]"},
        print_as_proof_forms,
    )
    # Task 10.5

    step1 = prover.add_assumption("~Ex[(Homework(x)&Fun(x))]")
    step2 = prover.add_assumption("Ex[(Homework(x)&Reading(x))]")
    step3 = prover.add_instantiated_assumption(
        "((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])",
        Prover.EI,
        {"R": "(Homework(_)&Fun(_))", "c": "x"},
    )
    step4 = prover.add_tautological_implication(
        "(~Ex[(Homework(x)&Fun(x))]->~(Homework(x)&Fun(x)))", {step3}
    )
    step5 = prover.add_mp("~(Homework(x)&Fun(x))", step1, step4)
    step6 = prover.add_tautological_implication(
        "((Homework(x)&Reading(x))->(Reading(x)&~Fun(x)))", {step5}
    )
    step7 = prover.add_instantiated_assumption(
        "((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])",
        Prover.EI,
        {"R": "(Reading(_)&~Fun(_))", "c": "x"},
    )
    step8 = prover.add_tautological_implication(
        "((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])", {step7, step6}
    )
    prover.add_existential_derivation("Ex[(Reading(x)&~Fun(x))]", step2, step8)

    return prover.qed()


#: The three group axioms
GROUP_AXIOMS = frozenset(
    {"plus(0,x)=x", "plus(minus(x),x)=0", "plus(plus(x,y),z)=plus(x,plus(y,z))"}
)


def prove_group_right_neutral(
    stop_before_flipped_equality: bool,
    stop_before_free_instantiation: bool,
    stop_before_substituted_equality: bool,
    stop_before_chained_equality: bool,
    print_as_proof_forms: bool = False,
) -> Proof:
    """Proves from the group axioms that x+0=x (``'plus(x,0)=x'``).

    Parameters:
        stop_before_flipped_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_flipped_equality` and to return the
            prefix of the proof created up to that point.
        stop_before_free_instantiation: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_free_instantiation` and to return the
            prefix of the proof created up to that point.
        stop_before_substituted_equality: flag specifying stop proving just
            before the first call to
            `~predicates.prover.Prover.add_substituted_equality` and to return
            the prefix of the proof created up to that point.
        stop_before_chained_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_chained_equality` and to return the
            prefix of the proof created up to that point.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS, print_as_proof_forms)
    zero = prover.add_assumption("plus(0,x)=x")
    negation = prover.add_assumption("plus(minus(x),x)=0")
    associativity = prover.add_assumption("plus(plus(x,y),z)=plus(x,plus(y,z))")
    if stop_before_flipped_equality:
        return prover.qed()
    flipped_zero = prover.add_flipped_equality("x=plus(0,x)", zero)
    flipped_negation = prover.add_flipped_equality(
        "0=plus(minus(x),x)", negation
    )
    flipped_associativity = prover.add_flipped_equality(
        "plus(x,plus(y,z))=plus(plus(x,y),z)", associativity
    )
    if stop_before_free_instantiation:
        return prover.qed()
    step7 = prover.add_free_instantiation(
        "0=plus(minus(minus(x)),minus(x))", flipped_negation, {"x": "minus(x)"}
    )
    step8 = prover.add_flipped_equality(
        "plus(minus(minus(x)),minus(x))=0", step7
    )
    step9 = prover.add_free_instantiation(
        "plus(plus(minus(minus(x)),minus(x)),x)="
        "plus(minus(minus(x)),plus(minus(x),x))",
        associativity,
        {"x": "minus(minus(x))", "y": "minus(x)", "z": "x"},
    )
    step10 = prover.add_free_instantiation("plus(0,0)=0", zero, {"x": "0"})
    step11 = prover.add_free_instantiation(
        "plus(x,0)=plus(0,plus(x,0))", flipped_zero, {"x": "plus(x,0)"}
    )
    step12 = prover.add_free_instantiation(
        "plus(0,plus(x,0))=plus(plus(0,x),0)",
        flipped_associativity,
        {"x": "0", "y": "x", "z": "0"},
    )
    if stop_before_substituted_equality:
        return prover.qed()
    step13 = prover.add_substituted_equality(
        "plus(plus(0,x),0)=plus(plus(plus(minus(minus(x)),minus(x)),x),0)",
        step7,
        "plus(plus(_,x),0)",
    )
    step14 = prover.add_substituted_equality(
        "plus(plus(plus(minus(minus(x)),minus(x)),x),0)="
        "plus(plus(minus(minus(x)),plus(minus(x),x)),0)",
        step9,
        "plus(_,0)",
    )
    step15 = prover.add_substituted_equality(
        "plus(plus(minus(minus(x)),plus(minus(x),x)),0)="
        "plus(plus(minus(minus(x)),0),0)",
        negation,
        "plus(plus(minus(minus(x)),_),0)",
    )
    step16 = prover.add_free_instantiation(
        "plus(plus(minus(minus(x)),0),0)=plus(minus(minus(x)),plus(0,0))",
        associativity,
        {"x": "minus(minus(x))", "y": "0", "z": "0"},
    )
    step17 = prover.add_substituted_equality(
        "plus(minus(minus(x)),plus(0,0))=plus(minus(minus(x)),0)",
        step10,
        "plus(minus(minus(x)),_)",
    )
    step18 = prover.add_substituted_equality(
        "plus(minus(minus(x)),0)=plus(minus(minus(x)),plus(minus(x),x))",
        flipped_negation,
        "plus(minus(minus(x)),_)",
    )
    step19 = prover.add_free_instantiation(
        "plus(minus(minus(x)),plus(minus(x),x))="
        "plus(plus(minus(minus(x)),minus(x)),x)",
        flipped_associativity,
        {"x": "minus(minus(x))", "y": "minus(x)", "z": "x"},
    )
    step20 = prover.add_substituted_equality(
        "plus(plus(minus(minus(x)),minus(x)),x)=plus(0,x)", step8, "plus(_,x)"
    )
    if stop_before_chained_equality:
        return prover.qed()
    step21 = prover.add_chained_equality(
        "plus(x,0)=x",
        [
            step11,
            step12,
            step13,
            step14,
            step15,
            step16,
            step17,
            step18,
            step19,
            step20,
            zero,
        ],
    )
    return prover.qed()


def prove_group_unique_zero(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms and from the assumption a+c=a
    (``'plus(a,c)=a'``) that c=0 (``'c=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS.union({"plus(a,c)=a"}), print_as_proof_forms)
    # Task 10.10

    negated_assum: int = prover.add_assumption("plus(minus(x),x)=0")
    neutral_assum: int = prover.add_assumption("plus(0,x)=x")
    associativity_asum: int = prover.add_assumption(
        "plus(plus(x,y),z)=plus(x,plus(y,z))"
    )

    line1: int = prover.add_assumption("plus(a,c)=a")
    line2: int = prover.add_free_instantiation(
        "plus(minus(a),a)=0", negated_assum, {"x": "a"}
    )
    line3: int = prover.add_substituted_equality(
        "plus(minus(a),plus(a,c))=plus(minus(a),a)", line1, "plus(minus(a),_)"
    )
    line4: int = prover.add_flipped_equality("0=plus(minus(a),a)", line2)
    line5: int = prover.add_free_instantiation(
        "plus(0,c)=c", neutral_assum, {"x": "c"}
    )
    line6: int = prover.add_substituted_equality(
        "plus(0,c)=plus(plus(minus(a),a),c)", line4, "plus(_,c)"
    )
    line7: int = prover.add_flipped_equality("c=plus(0,c)", line5)
    line8: int = prover.add_free_instantiation(
        "plus(plus(minus(a),a),c)=plus(minus(a),plus(a,c))",
        associativity_asum,
        {"x": "minus(a)", "y": "a", "z": "c"},
    )

    prover.add_chained_equality("c=0", [line7, line6, line8, line3, line2])

    return prover.qed()


#: The six field axioms
FIELD_AXIOMS = frozenset(
    GROUP_AXIOMS.union(
        {
            "plus(x,y)=plus(y,x)",
            "times(x,1)=x",
            "times(x,y)=times(y,x)",
            "times(times(x,y),z)=times(x,times(y,z))",
            "(~x=0->Ey[times(y,x)=1])",
            "times(x,plus(y,z))=plus(times(x,y),times(x,z))",
        }
    )
)


def prove_field_zero_multiplication(
    print_as_proof_forms: bool = False,
) -> Proof:
    """Proves from the field axioms that 0*x=0 (``'times(0,x)=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(FIELD_AXIOMS, print_as_proof_forms)
    # Task 10.11

    # Proof: 0*x=0 by (0*x)+(0*x)= 0*x and previous proof (a+c=c)->c=0

    distributive_axiom: int = prover.add_assumption(
        "times(x,plus(y,z))=plus(times(x,y),times(x,z))"
    )
    neutral_axiom: int = prover.add_assumption("plus(0,x)=x")
    mul_comm_axiom: int = prover.add_assumption("times(x,y)=times(y,x)")
    negated_axiom: int = prover.add_assumption("plus(minus(x),x)=0")
    associative_axiom: int = prover.add_assumption(
        "plus(plus(x,y),z)=plus(x,plus(y,z))"
    )

    def add_intermediate_proof() -> int:
        line1: int = prover.add_free_instantiation(
            "plus(0,0)=0", neutral_axiom, {"x": "0"}
        )
        flipped_zeroed_eq: int = prover.add_flipped_equality(
            "0=plus(0,0)", line1
        )

        line3: int = prover.add_free_instantiation(
            "times(x,0)=times(0,x)", mul_comm_axiom, {"x": "x", "y": "0"}
        )
        line4: int = prover.add_substituted_equality(
            "plus(times(x,0),times(0,x))=plus(times(0,x),times(0,x))",
            line3,
            "plus(_,times(0,x))",
        )
        line5: int = prover.add_substituted_equality(
            "plus(times(x,0),times(x,0))=plus(times(x,0),times(0,x))",
            line3,
            "plus(times(x,0),_)",
        )
        line6: int = prover.add_free_instantiation(
            "times(x,plus(0,0))=plus(times(x,0),times(x,0))",
            distributive_axiom,
            {"x": "x", "y": "0", "z": "0"},
        )
        line7: int = prover.add_substituted_equality(
            "times(x,0)=times(x,plus(0,0))", flipped_zeroed_eq, "times(x,_)"
        )
        line8: int = prover.add_free_instantiation(
            "times(0,x)=times(x,0)", mul_comm_axiom, {"x": "0", "y": "x"}
        )
        line9: int = prover.add_chained_equality(
            "times(0,x)=plus(times(0,x),times(0,x))",
            [line8, line7, line6, line5, line4],
        )

        return prover.add_flipped_equality(
            "plus(times(0,x),times(0,x))=times(0,x)", line9
        )

    def add_unique_zero_corollary() -> None:
        line11: int = add_intermediate_proof()

        a_c: str = "times(0,x)"
        line12: int = prover.add_substituted_equality(
            f"plus(minus({a_c}),plus({a_c},{a_c}))=plus(minus({a_c}),{a_c})",
            line11,
            f"plus(minus({a_c}),_)",
        )
        line13: int = prover.add_free_instantiation(
            f"plus(minus({a_c}),{a_c})=0", negated_axiom, {"x": a_c}
        )
        line14: int = prover.add_free_instantiation(
            f"plus(plus(minus({a_c}),{a_c}),{a_c})=plus(minus({a_c}),plus({a_c},{a_c}))",
            associative_axiom,
            {"x": f"minus({a_c})", "y": a_c, "z": a_c},
        )
        line15: int = prover.add_flipped_equality(
            f"0=plus(minus({a_c}),{a_c})", line13
        )
        line16: int = prover.add_substituted_equality(
            f"plus(0,{a_c})=plus(plus(minus({a_c}),{a_c}),{a_c})",
            line15,
            f"plus(_,{a_c})",
        )
        line17: int = prover.add_free_instantiation(
            f"plus(0,{a_c})={a_c}", neutral_axiom, {"x": a_c}
        )
        line18: int = prover.add_flipped_equality(
            f"{a_c}=plus(0,{a_c})", line17
        )
        prover.add_chained_equality(
            f"{a_c}=0", [line18, line16, line14, line12, line13]
        )

    add_unique_zero_corollary()

    return prover.qed()


#: Axiom schema of induction
INDUCTION_AXIOM = Schema(
    Formula.parse("((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])"), {"R"}
)
#: The seven axioms of Peano arithmetic
PEANO_AXIOMS = frozenset(
    {
        "(s(x)=s(y)->x=y)",
        "~s(x)=0",
        "plus(x,0)=x",
        "plus(x,s(y))=s(plus(x,y))",
        "times(x,0)=0",
        "times(x,s(y))=plus(times(x,y),x)",
        INDUCTION_AXIOM,
    }
)


def prove_peano_left_neutral(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms of Peano arithmetic that 0+x=x
    (``'plus(0,x)=x'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(PEANO_AXIOMS, print_as_proof_forms)
    # Task 10.12

    zero_as_right_neutral: int = prover.add_assumption("plus(x,0)=x")
    peano_axiom: int = prover.add_assumption("plus(x,s(y))=s(plus(x,y))")

    base_formula: str = "plus(0,0)=0"
    step_formula: str = "Ax[(plus(0,x)=x->plus(0,s(x))=s(x))]"
    induction_corollary: str = "plus(0,x)=x"
    induction_formula_line_num: int = prover.add_instantiated_assumption(
        f"(({base_formula}&{step_formula})->Ax[{induction_corollary}])",
        INDUCTION_AXIOM,
        {"R": "plus(0,_)=_"},
    )

    # induction step
    line1: int = prover.add_free_instantiation(
        "plus(0,s(x))=s(plus(0,x))", peano_axiom, {"x": "0", "y": "x"}
    )
    line2: int = prover.add_instantiated_assumption(
        "(plus(0,x)=x->(plus(0,s(x))=s(plus(0,x))->plus(0,s(x))=s(x)))",
        Prover.ME,
        {"R": "plus(0,s(x))=s(_)", "c": "plus(0,x)", "d": "x"},
    )
    line3: int = prover.add_tautological_implication(
        "(plus(0,x)=x->plus(0,s(x))=s(x))", {line2, line1}
    )
    induction_step: int = prover.add_ug(step_formula, line3)

    # induction base
    induction_base: int = prover.add_free_instantiation(
        base_formula, zero_as_right_neutral, {"x": "0"}
    )

    # conclusion
    base_and_step: int = prover.add_tautological_implication(
        f"({base_formula}&{step_formula})", {induction_base, induction_step}
    )
    ug_conclusion: int = prover.add_mp(
        f"Ax[{induction_corollary}]", base_and_step, induction_formula_line_num
    )

    prover.add_universal_instantiation(induction_corollary, ug_conclusion, "x")

    return prover.qed()


#: Axiom schema of (unrestricted) comprehension
COMPREHENSION_AXIOM = Schema(
    Formula.parse("Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]"), {"R"}
)


def prove_russell_paradox(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms schema of unrestricted comprehension the
    contradiction ``'(z=z&~z=z)'``.

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({COMPREHENSION_AXIOM}, print_as_proof_forms)
    # Task 10.13

    # contradiction implies contradiction is a tautology
    contradiction_as_taut: int = prover.add_tautology(
        "(((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))->(z=z&~z=z))"
    )

    UI_mapping: Dict[str, Union[Term, Formula]] = {
        "R": Formula.parse("((In(_,y)->~In(_,_))&(~In(_,_)->In(_,y)))"),
        "c": Term("y"),
    }

    contradiction_instantiated: int = prover.add_instantiated_assumption(
        Prover.UI.instantiate(UI_mapping), Prover.UI, UI_mapping
    )

    conclusion_as_taut: int = prover.add_tautological_implication(
        "(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->(z=z&~z=z))",
        {contradiction_instantiated, contradiction_as_taut},
    )

    instantiated_comprehension: int = prover.add_instantiated_assumption(
        COMPREHENSION_AXIOM.instantiate({"R": Formula.parse("~In(_,_)")}),
        COMPREHENSION_AXIOM,
        {"R": "~In(_,_)"},
    )

    prover.add_existential_derivation(
        "(z=z&~z=z)", instantiated_comprehension, conclusion_as_taut
    )

    return prover.qed()


def _prove_not_exists_not_implies_all(
    variable: str, formula: Formula, print_as_proof_forms: bool = False
) -> Proof:
    """Proves that
    ``'(~E``\ `variable`\ ``[~``\ `formula`\ ``]->A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        variable: variable name for the quantifications in the formula to be
            proven.
        formula: statement to be universally quantified, and whose negation is
            to be existentially quantified, in the formula to be proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4a


def _prove_exists_not_implies_not_all(
    variable: str, formula: Formula, print_as_proof_forms: bool = False
) -> Proof:
    """Proves that
    ``'(E``\ `variable`\ ``[~``\ `formula`\ ``]->~A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        variable: variable name for the quantifications in the formula to be
            proven.
        formula: statement to be universally quantified, and whose negation is
            to be existentially quantified, in the formula to be proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4b


def prove_not_all_iff_exists_not(
    variable: str, formula: Formula, print_as_proof_forms: bool = False
) -> Proof:
    """Proves that
    `equivalence_of`\ ``('(~A``\ `variable`\ ``[``\ `formula`\ ``]', 'E``\ `variable`\ ``[~``\ `formula`\ ``]')``.

    Parameters:
        variable: variable name for the quantifications in the formula to be
            proven.
        formula: statement to be universally quantified, and whose negation is
            to be existentially quantified, in the formula to be proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4c
