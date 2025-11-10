#import "template.typ": *
#import "@preview/wordometer:0.1.4": word-count, total-characters

#let target_date = datetime(year: 2026, month: 1, day: 23)
#show : official.with(
  title: [
    Finite Model Finding for Lean 4
  ],
  author: "Henrik Böving",
  email: "H.Boeving@campus.lmu.de",
  matriculation: [TODO],
  thesis-type: [Master's Thesis],
  advisor: [Prof. Dr. Jasmin Blanchette],
  supervisor: [Prof. Dr. Jasmin Blanchette],
  submission_date: target_date.display("[month repr:long] [day], [year]"),
  glossary: (
    (key: "DTT", short: "DTT", long: "Dependent Type Theory"),
    (key: "HOL", short: "HOL", long: "Higher Order Logic"),
    (key: "ITP", short: "ITP", long: "Interactive Theorem Proving"),
  ),
  abstract: [
    When conducting formalization projects, a significant time sink can be attempts to prove
    theorems that are not actually correct. This can, for example, occur due to subtle mistakes in
    definitions or forgetting to state an assumption. Counterexample-finding techniques can be used
    to reduce this time sink by identifying incorrect theorems before time is spent attempting
    to prove them.

    This thesis describes work on a new counterexample-finding tool for the Lean 4 proof assistant.
    Unlike previous approaches for counterexample-finding in dependent type theories, it relies on
    finite model finding. For this I identify a practically significant fragment of Lean's logic
    and develop a reduction from it to the Nunchaku finite model finder. In addition, I develop
    extensions to Nunchaku that allow it to handle the generated problems better.
  ],
  acknowledgement: [
    I would like to thank Jasmin Blanchette for his supervision and, in particular, sharing details
    about Nitpick that helped improve Nunchaku during this work. In addition, Simon Cruanes helped
    me a lot with the long-forgotten implementation details of Nunchaku. Furthermore, I would like
    to thank Abdalrhman Mohamed and Andrew Reynolds for implementing new features and fixing bugs
    in cvc5 that were crucial for this work. Joachim Breitner and Arthur Adjedj helped me navigate
    components of the Lean metaprogramming ecosystem I was previously unfamiliar with. Finally I
    would like to thank Siddharth Bhat for helping me with parts of the algorithmics for the
    monomorphization.
  ]
)
#show: word-count.with(exclude: (raw.where(block: true), <no-wc>))
#show figure.caption : set text(10pt)

= Introduction (1P) <sect_intro>

The growing pervasiveness and sophistication of modern computing systems has increased both their
susceptibility to faults and the scale of damage such faults can cause. Ensuring that critical
mistakes in software are identified before they lead to serious consequences is therefore a vital challenge.
An increasingly popular approach to tackling this challenge is the use of @ITP systems such as
Lean @lean4, Isabelle (TODO: what's the canonical Isabelle citation), and Rocq @rocq. However, developing correctness proofs
in these systems at the same time as developing definitions and theorem statements can turn out to
be quite frustrating. Often times definitions turn out to be subtly wrong or hypotheses in theorems
need to be strengthened in order to make them provable. Counterexample-finding techniques can help
mitigate this problem by helping users identify such issues early, before significant time is wasted
on unprovable goals.

For this reason, a variety of counterexample-finding techniques have been incorporated into @ITP
systems over the years. For example, Isabelle provides support for random testing,
bounded exhaustive testing, narrowing, and finite model finding, implemented in
Quickcheck @quickcheck and Nitpick @nitpick. In contrast, systems grounded in @DTT have
predominantly relied on random testing with tools such as QuickChick @quickchick and Plausible
@plausible. These tools attempt to synthesize a procedure that evaluates the theorem
statement for specific input values. This procedure is then executed repeatedly with random inputs
to search for counterexamples. While this technique is quite effective in general, it does have a
crucial limitation: If the inputs to the theorems are constrained by complicated invariants, it can
be quite difficult to generate candidates for evaluation that satisfy these preconditions.
For such theorems, finite model finders like Nitpick shine. Nitpick reduces the original theorem to
SAT and invokes a SAT solver to search for counterexamples. The SAT solver can then search for
inputs with invariants more directly, rather than relying on random generation to eventually find them.

In this thesis I describe the first finite model finding approach, integrated with a dependently
typed theorem prover, namely Lean. The core contribution is the reduction of a practically relevant
fragment of Lean to the input logic of Nitpick's spiritual successor, Nunchaku @nunchakudtt.
First I describe the general idea behind the reduction in @sect_reduct.
Then I discuss the design of the new Chako counterexample finder based on this reduction
in @sect_impl. Lastly, I present an evaluation of Chako on a few case studies in
@sect_case_studies and parts of the Lean standard library in @sect_eval.

#pagebreak(weak: true)

= Related Work (1P) <sect_related>
Many counterexample-finding techniques have been integrated with @ITP systems in the past. These techniques
can generally be located somewhere on a spectrum between concrete execution and fully symbolic
reasoning.

On the concrete end of the spectrum, the most widely deployed technique is the already mentioned
random testing. Popularized by Haskell's QuickCheck @haskellquickcheck, many @ITP systems provide
an implementation of random testing, such as Isabelle's Quickcheck @quickcheck, Agda's QuickCheck
@agdaquickcheck, PVS @pvsquickcheck, ACL2 @acl2cex, Lean's Plausible @plausible, and Rocq's
QuickChick @quickchick. The main strength of this approach is performance: Computers can generate and
evaluate many candidates within a short time span. As previously explained, the main weakness
is theorems with complex constraints on the input space that make it hard to generate valid inputs.
In order to counteract this, Isabelle, ACL2, and Rocq @quickchick-multirelations
implement techniques to derive generators for inputs that are constrained by certain kinds of
inductive relations.

Another concrete execution technique is bounded exhaustive testing, implemented as a
QuickChick extension @boundex-coq and in Isabelle's Quickcheck. Bounded exhaustive testing
generates and tests all possible inputs to a conjecture up to a certain bound (e.g. term size).
Unlike random testing, this ensures that all potentially relevant inputs within the search
space are actually tested. The main limitation is that we can only feasibly test up to a rather
small bound so big counterexamples will usually be missed.

A fundamental limitation of systems that rely purely on concrete execution is the inability to
refute propositions that are not executable. For example, to demonstrate that
$forall n : NN, exists m : NN, n + m = m$ is false using concrete execution, the system would
have to generate a value for $n$ and then try all possible values for $m$. Issues like this can be
addressed with techniques that make use of symbolic reasoning. Between the fully symbolic and fully
concrete ends of the spectrum, Isabelle's Quickcheck also implements a narrowing-based approach. The idea
of narrowing is to symbolically evaluate the proposition with partially instantiated terms first
and then refine them until a counterexample can be found.

On the far symbolic end of the spectrum, we can find techniques that perform reductions to SAT or SMT
solvers. These techniques can roughly be separated into finite model finding and counterexample-producing
decision procedures. The latter often occurs as a by-product of integrating SAT and SMT solvers with @ITP
systems, as done in Rocq's SMTCoq @smtcoq and Lean's lean-smt @leansmt/*(TODO: is there an Isabelle SMT integration that is counterexample producing) */. Finite model finding techniques enumerate all
potential finite models of a conjecture in search of a false model. This enumeration procedure is
usually powered by a reduction to SAT or SMT. Finite model finding has, so far, only been deployed
to Isabelle in the form of Nitpick @nitpick and Refute @refute.

#pagebreak(weak: true)

= Background (4-6P) <sect_background>
I begin by providing an overview of the fundamentals of the source and target languages involved in
the reduction, focusing on the fragments relevant to this work. Additional details are discussed
later in @sect_reduct and @sect_impl.

== Lean 4 (3P) <sect_lean4>
Lean 4 @lean4 is an open-source interactive theorem prover and functional programming language.
Originally developed by Leonardo de Moura at Microsoft Research and Sebastian Ullrich at KIT, it is
nowadays maintained by the Lean FRO with many open-source contributions by other volunteers. On the theorem
proving side, Lean's logic is a dependent type theory based on the Calculus of Inductive Constructions @coc @cic.
This base calculus is extended with several axioms, most notably quotients, function extensionality, and
choice. A thorough theoretical description of Lean's logic and its properties can be found
in the work of #cite(<mario-type-theory>, form: "prose") and #cite(<sebastianphd>, form: "prose").

The syntax of Lean's core expression language is given by the grammar:
$
  e ::= x | c | e " " e | lambda x : e . e | "let" x := e; e | forall x : e. e | "Sort" u
$
Just like the simply typed lambda calculus, it contains variables, constants, function application,
function abstraction, and let abstraction. Unlike the simply typed lambda calculus, it does not have a function
type $A -> B$ but instead the dependent function type $forall x : A . B$. The crucial
difference being that the _term_ variable $x$ may occur in the _type_ $B$, we say $B$ depends on
$x$. For example, we can denote the type of functions that take a natural number $n$ and return a number
less than $n$ as $forall n : NN, "Fin" n$. If $B$ does not depend on $x$, we usually write just
$A -> B$ instead.

Lean supports several kinds of constants, with the most prominent ones being definitions, theorems,
and inductive types. Definitions and theorems consist of a name, type or statement, and a body.
The body may refer to the definition recursively in the surface-level syntax.
While Lean internally desugars these recursive definitions into a non-recursive
representation, we will mostly work with the equations that get automatically
derived from the original syntax. Inductive types are the primary mechanism to introduce new types
in Lean. They are defined by listing their constructors, which specify the ways in which values of
the type can be built. A few examples of basic inductive types and definitions are given in @basic-inductives.

As alluded to in @basic-inductives by the `: Type` notation, these basic inductive types also have a type:
$"Type"$. In fact, Lean supports a whole hierarchy of types $"Type" : "Type" 1 : ... : "Type" u : "Type" (u + 1)$
in order to avoid type-theoretic versions of Russell's paradox. At the bottom of
this hierarchy sits the type of mathematical propositions $"Prop" : "Type"$. Both of these concepts
are unified with the expression $"Sort" u$ by defining $"Prop" := "Sort" 0$ and $"Type" u := "Sort" (u + 1)$.

#figure(
  ```lean
  inductive Unit : Type where
    | unit

  inductive Bool : Type where
    | true
    | false

  def Bool.not (b : Bool) : Bool :=
    match b with
    | true => Bool.false
    | false => Bool.true

  -- types may be recursive
  inductive Nat : Type where
    | zero
    | succ (n : Nat)

  -- types may contain proofs of invariants
  inductive Fin (n : Nat) : Type where
    | mk (val : Nat) (h : val < n)

  -- types may be generic over other types
  inductive Prod (α : Type) (β : Type) : Type where
    | mk (fst : α) (snd : α)

  def Prod.fst {α : Type} {β : Type} (p : Prod α β) : α :=
    match p with
    | .mk fst _ => fst

  -- dependent product type
  inductive Sigma (α : Type) (β : α → Type) : Type where
    | mk (fst : α) (snd : β fst)

  inductive List (α : Type) : Type where
    | nil
    | cons (x : α) (xs : List α)

  -- definitions may be recursive
  def List.length {α : Type} (xs : List α) : Nat :=
    match xs with
    | nil => Nat.zero
    | cons _ ys => Nat.succ (List.length ys)

  -- lists of length n
  inductive Vec (α : Type) : Nat → Type where
    | nil : Vec α 0
    | cons {n : Nat} (x : α) (xs : Vec α n) : Vec α (n + 1)
  ```,
  caption: "Basic Inductive Types and Definitions",
  gap: 1.5em,
) <basic-inductives>

#pagebreak(weak: true)

Proofs in Lean are done using the Curry-Howard correspondence: Given a type $P : "Prop"$, if we
can construct an inhabitant of that type $h : P$, then $h$ is a proof of $P$. The main
motivation for introducing $"Prop"$ as a separate concept is to allow for impredicativity and proof
irrelevance. That is, we have $(forall x : A, P) : "Prop"$ and for any two inhabitants
$h_1, h_2 : P$ we get $h_1 = h_2$ by definition. Proof irrelevance is going to be of particular
interest because it ensures that proof terms cannot be computationally relevant.
This allows us to always erase proofs without changing the semantics of a Lean program.

On top of these base concepts, Lean provides a myriad of additional concepts that all get reduced to
the core calculus through a process called elaboration. These reductions are performed by programs
called elaborators that are also written in Lean. The mechanism for integrating additional elaborators is so powerful
that completely new languages have been developed entirely as extensions to Lean itself. For
example, Veil @veil implements a language for defining and reasoning about distributed systems within
Lean.

On the type level, a very common extension is `structure`s. They are inductive types with only one
constructor. For each structure, Lean automatically derives projection functions to obtain each of the
parameters to that constructor. Using structures, the `Prod` definition from @basic-inductives could
have also been written as:
```lean
structure Prod (α : Type) (β : Type) where
  fst : α -- Prod.fst is defined implicitly
  snd : α
```
On the expression level, one of the most pervasive extensions is implicit parameters.
If a parameter is written `{x : A}` instead of `(x : A)`, Lean will attempt
to infer it from the other parameters. For example, the `List.length` function in @basic-inductives
will attempt to infer its type parameter `α` by inspecting the type of `xs`. Parameters written as
`[x : A]` are resolved using type class inference. Type classes are ordinary `inductive`s or
`structure`s that are tagged as a `class`. Type class inference performs a Prolog-like search
@tabled-typeclass through definitions of such classes that have been tagged as an `instance`.

The type class system is frequently used to provide user-extensible notations.
This is usually done by introducing a type class with a function field together with a notation that
maps to this function. With this approach, we might implement a user-extensible addition operator as follows:
#grid(
  columns: (1fr, 1fr),
  align: center,
```lean
class Add (α : Type) where
  add : α → α → α

-- Add.add implicitly takes [Add α]
notation " + " => Add.add
```,
```lean
instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add
```
)

#pagebreak(weak: true)

== Nunchaku (2P-3P) <sect_nunchaku>
@nitpick, @nitpickpred, @nunchakudtt, @smbc, @cvc4, @kodkod, @paradox
- explain relevant fragment of the input logic for nunchaku
  - basic expression language from HOL
  - `data`, `pred`, `axiom`, `val`, `goal`
- explain the general nunchaku architecture
  - micropass system for reducing from the original goal to the solver specific logic, then pulling
    results back along it.
  - pipeline data type?
- roughly explain the pipeline to CVC4 in its current stage
  - list out all of its steps first `--pp-pipeline`
  - describe the parts relevant to this work:
    - type skolemization and monomorphisation: Relevant because we need to show Lean's type theory
      needs more than this
    - specialisation: Relevant as this demonstrates how relevant removing HOF is
    - polarisation and unrolling: Relevant as this demonstrates how relevant `[wf]` annotations are
    - elimination of inductive predicates: Relevant to motivate that specialising again after this makes sense

#pagebreak(weak: true)

= Reduction (12 + 2P) <sect_reduct>
== Eliminating Dependent Types (8P) <sect_trans_dtt>
@nunchakudtt

/*
Idea: Generate invariant propositions and erase useless things.

Two steps of translation:
+ Get rid of dependent types in full generality by:
  - Erasing all proofs
  - For each dependent type generate a pure nondep data component and an invariant
  - Replace each occurrence of a dep type with a subtype of the nondep one with that invariant
  - Replace each occurrence of a type argument with a pair of type argument and predicate over that
    type (these predicates are threaded (potentially recursively through other functions) into
    invariants)
+ Erasing these subtypes by:
  - in all $forall$ binders in propositional context replacing them with a precondition and a normal
    binder over the type
  - in all $forall$ binders in non-prop context just dropping them, reason: The type system
    guarantees that the functions behind these forall binders are only called with valid arguments
    anyway
  - in all $lambda$ binders just dropping them (same reason)

Now we have banished the DTT world into inductive predicates where they are perfectly fine to live
on.

Interesting duality here: We could also try to monomorphize before doing this invariant
introduction, in this case the addition of predicates for type arguments would be unnecessary.
However, monomorphising DTT in full generality seems like a harder problem that this translation.

Note that this even works for nested inductives:
```lean
inductive Tree (α : Type) where
  | nil : Tree α
  | node (x : α) (xs : List (Tree α)) : Tree α

inductive ListInv (p : α → Prop) : List α → Prop where
  | nil : ListInv p List.nil
  | cons (x : α) (hx : p x) (xs : List α) (hxs : ListInv p xs) : ListInv p (x :: xs)

inductive Invariant (p : α → Prop) : Tree α → Prop where
  | nil : Invariant p Tree.nil
  | node (x : α) (hx : p x) (xs : List (Tree α)) (hxs : ListInv (Invariant p) xs) : Invariant p (Tree.node x xs)
```

note: When talking about erasure we could also replace it with `Unit` in order to not change arity
of symbols, will have to think about it

- type aliases,  it is crucial that this particular part happens everywhere to kill things such as
  `outParam` for the monomorphization
- literals
*/

== Eliminating Polymorphism (4P) <sect_trans_poly>

/*
This leaves us with an expression language consisting of:
$
  e := x | c | U_n | e " " e | forall (x : e), e | lambda (x : e), e
$
where $c$ can be:
- `inductive`
- `ctor`
- `def`
- `opaque`

TODO: cleanup step about about local type variables

Lean does allow for a much more general kind of polymorphism than Nunchaku can handle, in
particular:
- existential types
- higher ranked polymorphism
- non parametric polymorphism
- functions can compute types
  - due to this it can even be entirely unclear whether an argument is a value or type argument to
    begin with as this may depend on computation performed on other input parameters
  - TODO: our DTT eliminator already gives up on this but it is still interesting to consider this:

While things like existential types have been believed to be non monomorphisable recent advances in
this area @monotypeflow have demonstrated that a much wider range of type systems than previously
thought are admissible to monomorphization.

TODO: exposition about type flow analysis

For simplicity we consider all type arguments to be in the beginning. Furthermore type parameters
of the constructor of a generic type have the parameters for the type itself first and potential
existential ones later (bla bla about type indices illegal and what not). We define a function
$"tarity"(c)$ that returns how many type arguments a
function has. This is crucial as generic functions (and constructors) can be partially applied which we currently
don't support.

We now adapt this analysis to the remaining fragment of Lean. Relations:
- $Sigma tack e =>_E R$ collecting constraints on expressions
- $Sigma tack c " " e_1 ... e_n =>_A C$ collecting constraints for applied constants
- $Sigma tack c =>_C C$ collecting constraints that are inherent to constants

TODO handle lambda

#align(center, [
  #box(proof-tree(inf-rule(
    $Sigma tack x =>_E emptyset$,
    name: "Var"
  )))
  #box(proof-tree(inf-rule(
    $Sigma tack c =>_E R$,
    $Sigma tack c =>_C R$,
    name: "Const"
  )))
  #box(proof-tree(inf-rule(
    $Sigma tack U_n =>_E emptyset$,
    name: "Univ"
  )))
  #box(proof-tree(inf-rule(
    $Sigma tack forall (x : e_1), e_2 =>_E R_1 union R_2$,
    $Sigma tack e_1 =>_E R_1$,
    $Sigma tack e_2 =>_E R_2$,
    name: "Pi"
  )))
  #box(proof-tree(inf-rule(
    $Sigma tack c " " e_1 ... e_n =>_E R_c union union.big_i R_i$,
    $Sigma tack c " " e_1 ... e_(min(n, "tarity"(c))) =>_A R_c$,
    $forall i, Sigma tack e_i => R_i$,
    name: "ConstApp"
  )))
  #box(proof-tree(inf-rule(
    $Sigma tack e_1 " " e_2 ... e_n =>_E union.big_i R_i$,
    $forall i, Sigma tack e_i =>_E R_i$,
    name: "App"
  )))
])

#linebreak()
For the constraint collection of applied constants we have rules of the shape:

#align(center, [
#box(proof-tree(inf-rule(
  $Sigma tack c " " e_1 ... e_n =>_E { [e_i | i in [1, "tarity"(c)]] subset.eq.sq [alpha_i | i in [1, "tarity"(c)]] } union R_c$,
  $"inductive" c : alpha_1 -> ... -> alpha_("tarity"(c)) -> e "where" | ...  in Sigma$,
  $"tarity"(c) <= n$,
  $Sigma tack c =>_C R_c$,
  name: "IndApp"
)))])

#linebreak()
and similarly for all other constant kinds. This leaves only the constraints that are inherent to
constants:


#align(center, [
  #box(proof-tree(inf-rule(
    $Sigma tack c =>_C R_"ind" union union.big_i { [alpha_1, ..., alpha_("tarity"(c))] subset.sq.eq [beta_(i_1), ..., beta_(i_("tarity"(c)))] } union R_i $,
    $"inductive" c : alpha_1 -> ... -> alpha_("tarity"(c)) -> e_"ind" "where" | "ctor"_i : beta_(i_1) -> ... -> beta_(i_n) -> e_i in Sigma$,
    $forall i, Sigma tack e_i =>_E R_i$,
    $Sigma tack e_"ind" =>_E R_"ind"$,
    name: "Ind"
  )))
  #box(proof-tree(inf-rule(
    $Sigma tack c =>_C R$,
    $"inductive" c_"ind" : alpha_1 -> ... -> alpha_("tarity"(c_"ind")) -> e_"ind"  "where" | c " " : beta_(i_1) -> ... ->beta_(i_n) -> e_i in Sigma$,
    $Sigma tack c_"ind" =>_C R$,
    name: "Ctor"
  )))
  #box(proof-tree(inf-rule(
    $Sigma tack c =>_C union.big_i R_i$,
    $"def" c : alpha_1 -> ... -> alpha_("tarity"(c)) -> e_1 "with" e_2, ... e_n  in Sigma$,
    $forall i, Sigma tack e_i =>_E R_i$,
    name: "Defn"
  )))
  #box(proof-tree(inf-rule(
    $Sigma tack c =>_C R$,
    $"opaque" c : e in Sigma$,
    $Sigma tack e =>_E R$,
    name: "Opaque"
  )))
])

We run the $Sigma tack e =>_E R$ analysis for all variables in the local context of the goal as well
as the goal itself and thus transitively end up collecting constraints for all involved functions
and symbols in the entire problem. As with previous analyses it is crucial to cache results of
shared subterms (or rather just not visiting repeated subterms) to avoid blowup that could've been
caused by the initial reduction operations.

TODO: Talk about solvability

After constraint collection we solve it with a standard fixpoint solver for lattice constraints.

TODO talk about applying the results
*/

#pagebreak(weak: true)

= Implementation (5P) <sect_impl>

== The Lean Frontend (3P) <sect_impl_lean>
/*
The elimination is guided by a few core principles:
- try to stay in well typed Lean for as long as possible in order to:
  - make use of the extensive meta framework available in Lean
  - make use of the type checker for detecting bugs in the implementation during development time
- unlike a proof tactic, the reductions we perform do not have to be proof producing and can thus
  pull off some things that are not possible in usual Lean tactics
- aggressive use of shared subterms and caching of results


We eliminate:
+ comfort features:
  - universe parameters
    - can prove that we want to instantiate them with $1$ in order to avoid `Sort <stuff>` arguments
      falling into `Prop`
  - `let` in the local context
  - type arguments from the local context
+ Dependent types
  - using the translation from above
  - special casing a few things
    - logical connectives like `And`, `Or` etc.
    - `matcher` and `casesOn` with custom equations
    - literals:
      - mention issue with large nat literals
+ Monomorphisation
  - essentially a 1:1 implementation of the above algorithm

In addition to that we infer and annotate `[wf]` predicates for Nunchaku.
*/

== Extending Nunchaku (2P) <sect_impl_nunchaku>
/*
The following extensions to nunchaku are made to support this type of problem better:
- supporting specialisation for inductive predicates
- supporting erasure of unused arguments
- adding the cvc5 backend
- mention the fixed bugs
*/
#pagebreak(weak: true)

= Case Studies (4P) <sect_case_studies>
/*
- Case Studies:
  - reproducing grammar case study from @nitpickpred
  - reproducing type system case study from @nitpick
*/
#pagebreak(weak: true)

= Evaluation (2-3P) <sect_eval>
/*
- Large scale data:
  - evaluating on a chunk of lean stdlib + custom written libraries whether the system appears to
    be sound in practice despite its defficencies
  - mutating those theorems into false ones then evaluating on them to figure out counter example
    finding rate
*/

#pagebreak(weak: true)
= Outlook (1P) <sect_outlook>
/*
- Dealing with the function extensionality issue:
  - maybe by trying to eliminate the other way around
    - challenges that might arise from that so far unclear but things like existential type
      elimination likely gets a lot harder
- Further optimizing problems generated by nunchaku for solvers, it's still not quite on a level
  with what nitpick can do in isabelle
- Supporting more kinds of polymorphism:
  - HKTs
  - polymorphism over dependent types
  - existentials
*/

#v(15pt)
#[Total characters counted excluding code blocks: #total-characters] <no-wc>
