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
    components of the Lean metaprogramming ecosystem I was previously unfamiliar with.
  ]
)
#show: word-count.with(exclude: (raw.where(block: true), <no-wc>))
#show figure.caption : set text(10pt)

= Introduction (1P) <sect_intro>

// State of the art vs. contribution: You start by explaining the state of the art in
// your field. Do not hesitate to use the term state of the art to make this
// completely unambiguous for the reader. You then summarize your contribution.
// Do not hesitate to write contribution to make this clear

The growing pervasiveness and sophistication of modern computing systems has increased both their
susceptibility to faults and the scale of damage such faults can cause. Ensuring that critical
mistakes in software are identified before they lead to serious consequences is therefore a vital challenge.
An increasingly popular approach to tackling this challenge is the use of @ITP systems such as
Lean @lean4, Isabelle (TODO: cite), and Rocq @rocq. However, developing correctness proofs
in these systems at the same time as developing definitions and theorem statements can turn out to
be quite frustrating. Often times definitions turn out to be subtly wrong or hypotheses in theorems
need to be strengthened in order to make them provable. Counterexample-finding techniques can help
mitigate this problem by helping users identify such issues early, before significant time is wasted
on unprovable goals.

For this reason, a variety of counterexample-finding techniques have been incorporated into @ITP
systems over the years. For example, Isabelle provides support for random testing,
bounded exhaustive testing, narrowing, and finite model finding, as implemented in
Quickcheck @quickcheck and Nitpick @nitpick. In contrast, systems grounded in @DTT have
predominantly relied on random testing with tools such as QuickChick @quickchick and Plausible
#footnote[https://github.com/leanprover-community/plausible/]. Tools based on random testing
attempt to synthesize a procedure that evaluates the theorem statement for specific input values.
This procedure is then executed repeatedly with random inputs to search for counterexamples.
While this technique is quite effective in general, it does have a crucial limitation: If the inputs
to the theorems are constrained by complicated invariants, it can be quite difficult to generate
candidates for evaluation that satisfy these preconditions. For such theorems, finite model finders
like Nitpick shine. Nitpick reduces the original theorem to SAT and invokes a SAT solver to
search for counterexamples. The SAT solver can then search for inputs with invariants more
directly, rather than relying on random generation to eventually find them.

In this thesis I describe the first finite model finding approach, integrated with a dependently
typed theorem prover, namely Lean. The core contribution is the reduction of a practically relevant
fragment of Lean to the input logic of Nitpick's spiritual successor, Nunchaku @nunchakudtt.
First I describe the general idea behind the reduction in @sect_reduct.
Then I discuss the design of the new Chako counterexample finder based on this reduction
in @sect_impl. Lastly, I present an evaluation of Chako on a few case studies in
@sect_case_studies and parts of the Lean standard library in @sect_eval.

#pagebreak(weak: true)

= Related Work (1-1.5P) <sect_related>


#pagebreak(weak: true)

= Background (4-6P) <sect_background>
== Lean 4 (2P-3P) <sect_lean4>
@lean4, @sebastianphd
- explain basics of Lean
- focus on the fragment we are interested in:
  - `inductive`
  - `def`
  - `theorem`
  - `instance`
- talk about why we will think of lean definitions being defined in terms of equations

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

== Eliminating Polymorphism (4P) <sect_trans_poly>

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

#pagebreak(weak: true)

= Implementation (5P) <sect_impl>

== The Lean Frontend (3P) <sect_impl_lean>
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

== Extending Nunchaku (2P) <sect_impl_nunchaku>
The following extensions to nunchaku are made to support this type of problem better:
- supporting specialisation for inductive predicates
- supporting erasure of unused arguments
- adding the cvc5 backend
- mention the fixed bugs
#pagebreak(weak: true)

= Case Studies (4P) <sect_case_studies>
- Case Studies:
  - reproducing grammar case study from @nitpickpred
  - reproducing type system case study from @nitpick

= Evaluation (2-3P) <sect_eval>
- Large scale data:
  - evaluating on a chunk of lean stdlib + custom written libraries whether the system appears to
    be sound in practice despite its defficencies
  - mutating those theorems into false ones then evaluating on them to figure out counter example
    finding rate

#pagebreak(weak: true)
= Outlook (1P) <sect_outlook>
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


#v(15pt)
#[Total characters counted excluding code blocks: #total-characters] <no-wc>
