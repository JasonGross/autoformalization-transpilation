(** * Preface: Introduction to the Course *)

(* ################################################################# *)
(** * Welcome *)

(** This electronic book is Volume 6 of the _Software Foundations_ series, which
    presents the mathematical underpinnings of reliable software.

    *COMPANION COURSE NOTES*: A large part of this course is also written up in
    traditional LaTeX-style presentation. It's available from
    [http://www.chargueraud.org/teach/verif/slf_notes.pdf].

    This book will teach you about the foundations of Separation Logic, a
    practical approach to the modular verification of imperative programs. In
    particular, it presents the building blocks for constructing a program
    verification tool. It does not, however, focus on reasoning about data
    structures and algorithms using Separation Logic. This aspect is covered to
    some extent by Volume 5 of _Software Foundations_, which presents Verifiable
    C, a program logic and proof system for C. For OCaml programs, this aspect
    will be covered in a yet-to-be-written volume presenting CFML, a tool that
    builds upon all the techniques presented in this volume.

    You are only assumed to understand the material in _Software Foundations_
    Volume 1 (_Logical Foundations_), and the two chapters on Hoare Logic (Hoare
    and Hoare2) from Software Foundations Volume 2 (_PL Foundations_). Volume 5
    is not a prerequisite. The exposition here is intended for a broad range of
    readers, from advanced undergraduates to PhD students and researchers. *)

(* ################################################################# *)
(** * Separation Logic *)

(** Separation Logic is a _program logic_: it enables one to establish that a
    program satisfies its specification. Specifications are expressed using
    triples of the form [{H} t {Q}]. Whereas in Hoare logic the precondition [H]
    and the postcondition [Q] describe the whole memory state, in Separation
    Logic [H] and [Q] describe only a fragment of the memory state that includes
    the resources necessary to the execution of [t].

    A key ingredient of Separation Logic is the frame rule, which enables
    modular proofs. It is stated as follows.

         { H } t { Q }
    -------------------------
     { H \* H' } t { Q \* H' }

    The above rule asserts that if, a term [t] executes correctly with the
    resources [H] and produces [Q], then [t] admits the same behavior in a
    larger memory state, described by the union of [H] with a disjoint component
    [H'], producing the postcondition [Q] extended with that same resource [H']
    unmodified. The star symbol [\*] denotes the _separating conjunction_
    operator of Separation Logic.

    Separation Logic can be exploited in three kind of tools.

    - Automated proofs: the user provides only the code, and the tool
      locates sources of potential bugs. A good automated tool provides
      feedback that (at least most of time) is relevant.
    - Semi-automated proofs: the user provides not just the code,
      but also specifications and invariants. The tool then leverages
      automated solvers (e.g., SMT solvers) to discharge proof obligations.
    - Interactive proofs: the user provides not just the code and its
      specifications, but also a detailed proof script justifying the
      correctness of the code. These proofs may be developed interactively
      using a proof assistant such as Coq.

    The present course focuses on the third approach, that is, the integration
    of Separation Logic in an interactive proof assistant. This approach has
    been successfully put to practice throughout the world, using various proof
    assistants (Coq, Isabelle/HOL, HOL), targeting different languages
    (Assembly, C, SML, OCaml, Rust...) and for verifying various kind of
    programs, ranging from low-level operating system kernels to high-level data
    structures and algorithms. *)

(* ################################################################# *)
(** * Separation Logic in a Proof Assistant *)

(** The benefits of exploiting Separation Logic in a proof assistant include at
    least four major points:

    - higher-order logic provides virtually unlimited expressiveness
      that enables formulating arbitrarily complex specifications and
      invariants;
    - a proof assistant provides a unified framework to prove both
      the implementation details of the code and the underlying
      mathematical results, e.g., results from number theory or graph
      theory;
    - proof scripts may be easily maintained to reflect changes
      to the source code; and
    - the fact that Separation Logic itself is formalized in the proof
      assistant provides high confidence in the correctness of the tool.

    Pretty much all the tools that leverage Separation Logic in proof assistants
    are constructed following the same schema:

    - A formalization of the syntax and semantics of the source language.
      This is called a _deep embedding_ of the programming language.
    - A definition of Separation Logic predicates as predicates in
      higher-order logic. This is called a _shallow embedding_ of the
      program logic.
    - A definition of Separation Logic triples as a predicate, the
      statements of the reasoning rules as lemmas, and the proof of
      these reasoning rules with respect to the semantics.
    - An infrastructure that consists of lemmas, tactics and notations,
      allowing for the verification of concrete programs to be carried out
      through relatively concise proof scripts.
    - Applications of this infrastructure to the verification of concrete
      programs.

    The purpose of this course is to explain how to set up such a construction.
    To that end, we consider in this course the simplest possible variant of
    Separation Logic, and apply it to a minimalistic imperative programming
    language. The language essentially consists of a lambda-calculus with
    references. This language admits a simple semantics. It avoids, in
    particular, the need to distinguish between stack variables and heap-
    allocated variables. Advanced chapters later in the course explain how to
    add support for loops, records, arrays, and n-ary functions. *)

(* ################################################################# *)
(** * Multiple Reading Depths *)

(** All chapters except the first one are organized in three parts.

    - The _First Pass_ section presents the most important ideas only.
      The course in designed in such a way that it is possible to read only
      the _First Pass_ section of every chapter. The reader may be interested
      in going through all these sections to get the big picture, before
      revisiting each chapter in more detail.
    - The _More Details_ section presents additional material explaining
      in more depth the meaning and the consequences of the key results.
      This section also contains descriptions of the most important proofs.
      By default, readers would eventually read all this material.
    - The _Optional Material_ section typically contains the remaining
      proofs, as well as discussions of alternative definitions. The _Optional
      Material_ sections are all independent from each other. These sections
      are intended for (1) readers who plan to continue studying Separation
      Logic beyond the present course, and (2) teachers using the course. *)

(* ################################################################# *)
(** * Chapters Overview *)

(** The first two chapters, [Basic] and [Repr], give a primer on how
    to prove imperative programs in Separation Logic, i.e. they focus on the end
    user's perspective. The eight following chapters focus on the implementor's
    perspective, explaining how Separation Logic is defined and how a practical
    verification tool can be constructed. The last three chapters cover language
    extensions, from the perspective of both the user and the implementor.

    The list of chapters appears below. The numbering corresponds to _teaching
    units_: if the chapters were taught as part of a University course, one
    could reasonably aim to cover one teaching unit per week.

    - (1) [Basic]: introduction to the core features of Separation Logic,

    - (2) [Repr]: introduction to representation predicates in Separation
          Logic, in particular for describing mutable lists and trees.

    - (2) [Hprop]: definition of the core operators of Separation Logic.

    - (2) [Himpl]: definition of the entailment relation, statement and
          proofs of its fundamental properties, and description of the
          simplification tactic for entailment.

    - (3) [Triples]: definition of Separation Logic triples in terms
          of the semantics of the programming language.

    - (3) [Rules]: statement and proofs of the reasoning rules of
          Separation Logic, and example proofs of programs using these rules.

    - (4) [Wand]: introduction of the magic wand operator and other
          Separation Logic operators, and to the ramified frame rule.

    - (4) [WPsem]: definition of the semantic notion of weakest
          precondition, and statement of rules in weakest-precondition style.

    - (5) [WPgen]: presentation of a function that effectively computes
          the weakest precondition of a term, independently of its
          specification.

    - (5) [WPsound]: soundness proof for the weakest precondition
          generator (mostly optional).

    - (6) [Affine]: description of a generalization of Separation Logic
          with affine heap predicates, which are useful, in particular, for
          handling garbage-collected programming languages.

    - (6) [Arrays]: specification of both ML-style arrays with headers
          and C-style arrays with pointer arithmetic.

    - (6) [Records]: representation predicate for records, allowing us to
          isolate arbitrary subsets of a record's fields. *)

(* ################################################################# *)
(** * Other Distributed Files *)

(** The chapters listed above depend on a number of auxiliary files, which the
    reader does not need to go through but might be interested in looking at,
    either by curiosity, or for checking out a specific implementation detail.

    - [LibSepReference]: a long file that defines the program
      verification tool that is used in the first two chapters, and whose
      implementation is discussed throughout the other chapters. Each
      chapter from the course imports this module, as opposed to importing
      earlier chapters.

    - [LibSepVar]: a formalization of program variables, together with
      a bunch of notations for parsing variables.

    - [LibSepFmap]: a formalization of finite maps, which are used for
      representing the memory state.

    - [LibSepSimpl]: a functor that implements a powerful tactic for
      automatically simplifying entailments in Separation Logic.

    - [LibSepMinimal]: a minimalistic formalization of a soundness proof
      for Separation Logic, up to the verification of the [incr] function.

    - All other [Lib*] files are imports from the TLC library, which is
      described next. *)

(** The TLC library is a collection of general purpose theory and tactics
    developed over the years by Arthur Charguéraud. The TLC library is exploited
    in this course to streamline the presentation. TLC provides, in particular,
    extensions for classical logic and tactics that are particularly well suited
    for meta-theory. Prior knowledge of TLC is not required, and all exercises
    can be completed without using TLC tactics.

    The classical logic aspects of TLC are presented in chapter [Hprop].
    Each TLC tactic is introduced when it is first used. Most of these tactics
    are also presented in the chapter [UseTactics] of Software
    Foundations Volume 2 (_Programming Language Foundations_). *)

(* ################################################################# *)
(** * Practicalities *)

(* ================================================================= *)
(** ** System Requirements *)

(** Install instructions for Coq and IDEs may be found on this page:
    [https://www.chargueraud.org/teach/verif/install/install.html]

    The files you are reading have been tested with Coq version 8.19.2 but
    may also work with other versions. *)

(* ================================================================= *)
(** ** Feedback Welcome *)

(** If you intend to use this course either in class of for self-study, the
    author would love to hear from you. Just knowing in which contexts the
    course has been used and how much of the text students were able to cover is
    very valuable information.

    You can send feedback to slf --at-- chargueraud.org.

    If you plan on providing any non-small amount of feedback, do not hesitate
    to ask the author to be added as contributor to the github repository. *)

(* ================================================================= *)
(** ** Exercises *)

(** Each chapter includes numerous exercises. The star rating scheme is
    described in the [Preface] of Software Foundations Volume 1 (_Logical
    Foundations_).

    _Disclaimer_: the difficulty ratings currently in place are fairly
    speculative. You feedback is very much welcome.

    _Disclaimer_: (for instructors) the auto-grading system has not been tested
    for this volume. If you are interested in using auto-grading for this
    volume, please contact the author. *)

(* ================================================================= *)
(** ** Recommended Citation Format *)

(** If you want to refer to this volume in your own writing, please do so as
    follows:

    @book            {Chargueraud:SF6,
    author       =   {Arthur Charguéraud},
    editor       =   {Benjamin C. Pierce},
    title        =   "Separation Logic Foundations",
    series       =   "Software Foundations",
    volume       =   "6",
    year         =   "2024",
    publisher    =   "Electronic textbook",
    note         =   {Version 2.2, \URL{http://softwarefoundations.cis.upenn.edu} },
    }
*)

(* ################################################################# *)
(** * Thanks *)

(** The development of the technical infrastructure for the _Software
    Foundations_ series has been supported, in part, by the National Science
    Foundation under the NSF Expeditions grant 1521523, _The Science of Deep
    Specification_. *)

(* 2024-12-26 10:22 *)
