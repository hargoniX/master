#import "template.typ": *
#import "@preview/wordometer:0.1.4": word-count, total-characters

#set raw(syntaxes: "nunchaku.sublime-syntax")

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

= Introduction <sect_intro>

The growing pervasiveness and sophistication of modern computing systems has increased both their
susceptibility to faults and the scale of damage such faults can cause. Ensuring that critical
mistakes in software are identified before they lead to serious consequences is therefore a vital challenge.
An increasingly popular approach to tackling this challenge is the use of @ITP systems such as
Lean @lean4, Isabelle (TODO: what's the canonical Isabelle citation), and Rocq @rocq. However, developing correctness proofs
in these systems at the same time as developing definitions and theorem statements can turn out to
be quite frustrating. Often times definitions turn out to be subtly wrong or hypotheses in theorems
need to be strengthened to make them provable. This problem can be partially mitigated through the
use of counterexample-finding techniques. These techniques can help users identify such issues early,
before significant time is wasted on unprovable goals.

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
For such theorems, finite model finders such as Nitpick shine. Nitpick reduces the original theorem to
SAT and invokes a SAT solver to search for counterexamples. The SAT solver can then search for
inputs with invariants more directly, rather than relying on random generation to eventually find them.

In this thesis I describe the first finite model finding approach that is integrated with a dependently
typed theorem prover, namely Lean. The core contribution is the reduction of a practically relevant
fragment of Lean to the input logic of Nitpick's spiritual successor, Nunchaku @nunchakudtt.
First I describe the general idea behind the reduction in @sect_reduct.
Then I discuss the design of the new Chako counterexample finder based on this reduction
in @sect_impl. Lastly, I present an evaluation of Chako on a few case studies in
@sect_case_studies and parts of the Lean standard library in @sect_eval.

#pagebreak(weak: true)

= Related Work <sect_related>
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
In order to counteract this, Isabelle's Quickcheck, ACL2, and later iterations of Rocq's QuickChick @quickchick-multirelations
implement techniques to derive generators for inputs that are constrained by certain kinds of
inductive relations.

Another concrete execution technique is bounded exhaustive testing, implemented as a
QuickChick extension @boundex-coq and in Isabelle's Quickcheck. Bounded exhaustive testing
generates and tests all possible inputs to a conjecture up to a certain bound (e.g. term size).
Unlike random testing, this ensures that all potentially relevant inputs within the search
space are actually tested. The main limitation is that the search space can often only be fully
explored up to a small bound within a small time frame. This causes bounded exhaustive testing to
usually miss larger counterexamples.

A fundamental limitation of systems that rely purely on concrete execution is the inability to
refute propositions that are not executable. For example, to demonstrate that
$forall n : NN. exists m : NN. n + m = m$ is false using concrete execution, the system would
need to generate a value for $n$ and then try all possible values for $m$. Issues such as this can be
addressed with techniques that make use of symbolic reasoning.

Between the fully symbolic and fully concrete ends of the spectrum, Isabelle's Quickcheck also
implements a narrowing-based approach. The idea of narrowing is to symbolically evaluate the
proposition with partially instantiated terms first and then refine them until a counterexample can be found.

On the far symbolic end of the spectrum, we can find techniques that perform reductions to SAT or SMT
solvers. These techniques can roughly be separated into finite model finding and counterexample-producing
decision procedures. The latter often occurs as a by-product of integrating SAT and SMT solvers with @ITP
systems, as done in Rocq's SMTCoq @smtcoq and Lean's lean-smt @leansmt/*(TODO: is there an Isabelle SMT integration that is counterexample producing) */. Finite model finding techniques enumerate all
potential finite models of a conjecture in search of a false model. This enumeration procedure is
usually powered by a reduction to SAT or SMT. Finite model finding has, so far, only been deployed
to Isabelle in the form of Nitpick @nitpick and Refute @refute.

#pagebreak(weak: true)

= Background <sect_background>
I begin by providing an overview of the fundamentals of the source and target languages involved in
the reduction, focusing on the fragments relevant to this work. Additional details are discussed
later in @sect_reduct and @sect_impl.

== Lean 4 <sect_lean4>
Lean 4 @lean4 is an open-source interactive theorem prover and functional programming language.
Originally developed by Leonardo de Moura at Microsoft Research and Sebastian Ullrich at KIT, it is
nowadays maintained by the Lean FRO with many open-source contributions by other volunteers. On the theorem
proving side, Lean's logic is a dependent type theory based on the Calculus of Inductive Constructions @coc @cic.
This base calculus is extended with several axioms, most notably quotients, function extensionality, and
choice. A thorough theoretical description of Lean's logic and its properties can be found
in the work of Carneiro @mario-type-theory and Ullrich @sebastianphd.

The syntax of Lean's core expression language is given by the grammar:
$
  e ::= x | c | e " " e | lambda x : e . e | "let" x : e := e; e | (x : e) -> e | "Sort" u
$
Just like the simply typed lambda calculus, it contains variables, constants, function application,
function abstraction, and let abstraction. Unlike the simply typed lambda calculus, it does not have a function
type $A -> B$ but instead the dependent function type $(x : A) -> B$. The crucial
difference being that the _term_ variable $x$ may occur in the _type_ $B$, we say $B$ depends on
$x$. For example, we can denote the type of functions that take a natural number $n$ and return a number
less than $n$ as $(n : NN) -> "Fin" n$. If $B$ does not depend on $x$, we usually write just
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
irrelevance. That is, we have $(forall x : A. P) : "Prop"$ and additionally for any two inhabitants
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
@tabled-typeclass through definitions of class types that have been tagged as an `instance`.

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

== Nunchaku <sect_nunchaku>
Nunchaku @nunchakudtt is an open-source finite model finder. It is the spiritual successor
to Nitpick and was developed by Simon Cruanes and Jasmin Blanchette at INRIA.
Unlike Nitpick, Nunchaku is not tied to Isabelle as the input language and Kodkod @kodkod
as the backend solver. Instead, it consumes an idiosyncratic variant of classical @HOL @holbook and
has a family of backend solvers consisting of Kodkod, CVC4 @cvc4, SMBC @smbc, and Paradox @paradox.
Unfortunately, no publication about the overall design of Nunchaku has been made to date.
Therefore, the following section is largely based on reading the implementation and talking to
its authors.

Nunchaku's type and term language is based on @HOL, enriched with several built-in concepts. The
relevant fragment for this work is given by the following grammar:
$
  alpha ::=& "type" | "prop" | x | alpha -> alpha | c " " overline(alpha) | Pi x . alpha & "   " & "types"  \
  t ::=& c | x | t " " t | lambda x : alpha . t | "let" x : alpha := t; t | forall x : alpha . t | exists x : alpha . t \
    & | top | bot | not t | t or t | t and t | t => t | t = t | "if" t "then" t "else" t & "   " & "terms" \
$

The terms $t$ range over the usual connectives of simply typed lambda calculus, extended with
basic quantifiers and propositional connectives. The types $alpha$ consist of the universe of types,
the universe of propositions, type variables, function types, constants applied to type arguments ($overline(alpha)$
denotes a sequence of type arguments), and abstraction over type arguments.

The primary commands used to describe a Nunchaku problem are `val`, `axiom`, and `goal`.
The `val` command introduces uninterpreted constants for which Nunchaku must construct a model.
This model must ensure that the conjunction of all `axiom` predicates entails the conjunction of all
`goal` predicates.

For defining interpreted constants, Nunchaku has three main commands: `pred`, `data`, and `rec`.
Both `data` and `rec` operate similarly to Haskell, with `data` allowing definitions of polymorphic
algebraic types and `rec` allowing definitions of recursive functions by listing equations
they must fulfill. Lastly, `pred` provides a way to define inductive predicates by specifying their
introduction rules, similar to Isabelle or Lean. Using these basic commands, we can ask
Nunchaku for a counter-model of "adding two odd numbers yields an odd one":

#grid(
  columns: (1.1fr, 0.9fr),
  align: center,
```nun
data nat := Z | S nat.

rec add : nat -> nat -> nat :=
  forall x. add Z x = x;
  forall x y. add (S x) y = S (add x y).

pred odd : nat -> prop :=
  odd (S Z);
  forall n. odd n => odd (S (S n)).
```,
```nun
val n : nat.
axiom odd n.

val m : nat.
axiom odd m.

goal ~odd (add n m).
```
)

In order to solve these problems, Nunchaku applies long pipelines of reduction passes that eventually
end up in the input logics of its solvers. With the CVC4 pipeline alone containing 21 passes,
explaining the pipelines in full would be far out of scope for this work. Instead, the following
description focuses on the key steps relevant for the design of the reduction from Lean to
Nunchaku.

The first step across all pipelines is the elimination of polymorphism through monomorphization. The monomorphizer
removes all polymorphism by creating specialized copies of polymorphic constants, instantiated with
the type arguments they are used with. To simplify this process, Nunchaku imposes two restrictions
on its polymorphism. First, it supports only ML-style rank-1 polymorphism, meaning that a function
can be polymorphic, but it cannot take an argument that is itself polymorphic. Second, it does
not support higher-kinded types: $Pi$ may abstract over types but not type constructors.

After eliminating polymorphism, Nunchaku performs a few additional passes to remove other
convenience features before arriving at the specialization pass. Specialization is an optimization
that attempts to eliminate higher-order functions from the problem. It does so by first identifying
higher-order arguments of `rec` functions that remain fixed in all recursive calls. Once these arguments
are identified, Nunchaku inspects the call sites of the `rec`s and generates copies with the
concrete higher-order arguments substituted in.

In the following example specialization can eliminate the higher-order function `map`:
```nun
rec map : (nat -> nat) -> list -> list :=
  forall f. map f Nil = Nil;
  forall f x xs. map f (Cons x xs) = Cons (f x) (map f xs).

val xs : list.
goal map (add Z) xs != xs.
```
As we can see in the definition of `map`, the higher-order argument `f` always remains fixed in
recursive calls. For this reason, Nunchaku decides to create a copy of `map`, specialized on the
`add Z` function. This transformation turns the problem into an entirely first order one:
```nun
rec map_spec : list -> list :=
  map_spec Nil = Nil;
  forall x xs. map_spec (Cons x xs) = Cons (add Z x) (map_spec xs).

val xs : list.
goal map_spec xs != xs.
```

The last important pass for this work is the elimination of `pred` into `rec`. It is heavily
inspired by the encoding of inductive predicates used by Nitpick @nitpickpred. The encoding is
based on the fact that given an inductive predicate $p$ of the shape:
$
  & "pred" p : alpha_1 -> ... -> alpha_m -> "prop" "where" \
  & forall overline(y)_1 . p " " overline(t)_11 and ... and p " " overline(t)_(1cal(l)_1) and Q_1 => p " " overline(u)_1 \
  & dots.v \
  & forall overline(y)_n . p " " overline(t)_(n 1) and ... and p " " overline(t)_(n cal(l)_n) and Q_n => p " " overline(u)_n\
$
where the arguments $t_(i j)$ to $p$ and the side conditions $Q_i$ do not refer to $p$, $p$ is
equivalent to the least fixpoint of the equation @paulson-indpred @harrison-indpred: #footnote[Due to the mentioned syntactic restrictions
this fixpoint always exists by the Knaster-Tarski theorem]
$
  p " " overline(x) = (exists overline(y). or.big_(j = 1)^n overline(x) = overline(u)_j and p " " overline(t)_(j 1) and ... and p " " overline(t)_(j cal(l)_j) and Q_j)
$
While we could already take this equation as the definition of $p$, this is generally unsound because
it underspecifies $p$. However, there are two cases for which this is sound.

The first case concerns negative occurrences of $p$. To identify these, Nunchaku performs a
preprocessing step called polarization before predicate elimination. The polarizer traverses the
problem and determines the polarity in which applications of inductive predicates occur.
Each predicate $p$ is then replaced by two variants, $p^-$ and $p^+$, used in negative and
positive contexts, respectively.

During predicate elimination, occurrences of $p^-$ get transformed into `rec` definitions whose
bodies correspond to the right-hand side of the fixpoint equation. This transformation is sound
because $p$ represents a least fixpoint and is thus overapproximated by $p^-$, which admits any fixpoint:
$forall overline(x) . p " " overline(x) => p^- " " overline(x)$. From this, soundness for negative contexts follows
by contraposition: $forall overline(x) . not p^- " " overline(x) => not p " " overline(x)$.

The second case concerns the remaining positive occurrences of $p$. If the recursion in the
corresponding fixpoint equation is well-founded, the equation has exactly one solution @harrison-indpred.
This allows us to use the fixpoint equation as the definition for $p^+$ as well. For the recursion
to be well-founded, there needs to exist a relation $R$ such that:
$
  and.big_(i=1)^n and.big_(j=1)^(cal(l)_i) (Q_i => (overline(t)_(i j), overline(u)_i) in R)
$
This is where Nunchaku takes a deviation from Nitpick. In Nitpick the system itself will attempt to
find such a relation, while Nunchaku relies on the input problem to mark well-founded predicates.

Lastly, for inductive predicates that occur positively and do not fulfill the well-foundedness
criterion, Nunchaku converts them into well-founded ones. This is done by introducing an additional
fuel parameter of type $"nat"$ that decreases in each recursive call to the definition of $p$.
Along with this parameter, it introduces another uninterpreted constant $p_"decr" : "nat"$ that is
added to each application of $p$. Because the fuel decreases in every call, the recursion is
guaranteed to be well-founded and the predicate can be eliminated.

As an example for this consider the $<=$ predicate on natural numbers:
```nun
pred nat_le : nat -> nat -> prop :=
  forall n. nat_le n n;
  forall n m. nat_le n m => nat_le n (Succ m).
```
For negative occurrences this yields:
```nun
rec nat_le- : nat -> nat -> prop :=
  forall l r . nat_le- l r =
    exists m. l = r || (r = S m && nat_le- l m).
```
If the predicate would be (correctly) marked as `[wf]` by the problem, the body of `nat_le-`
would also be used for `nat_le+`. Given that it is not marked as `[wf]` here, Nunchaku also
generates:
```nun
rec nat_le+ : nat -> nat -> nat -> prop :=
  forall l r. nat_le+ Z l r = false;
  forall f l r. nat_le+ (S f) l r =
    exists m. l = r || (r = S m && nat_le+ f l m).
```

#pagebreak(weak: true)

= Reduction from Lean to Nunchaku (12 + 2P) <sect_reduct>
Designing a reduction from Lean's logic into Nunchaku's requires addressing the two key
differences between them: Lean's dependent types and Lean's more expressive polymorphism.
Instead of attempting to handle both of these in full generality, this section identifies
a fragment of Lean that is reasonably easy to translate and defines a reduction for this
fragment.

The differences between Lean's and Nunchaku's polymorphism are manifold. On the tamer side, Lean
supports many constructs that are present in other functional languages such as Haskell.
For example, it allows higher-ranked polymorphism, meaning that a function may take another
polymorphic function as an argument, e.g., `Nat → ((α : Type) → α → α) → Nat`. Lean also supports
higher-kinded types, which enable abstraction over type constructors, e.g.,
`(f : Type → Type) → f a → (a → b) → f b`. Finally, Lean provides existential types,
allowing constructors to bind type arguments, e.g., a type `Dynamic : Type 1` may have a constructor
of type `(α : Type) → α → Dynamic`.

Beyond these more "common" constructs, Lean also allows for arbitrary computation with types. For example,
we can define the type of $n$-ary products of natural numbers:
```lean
def NProd (n : Nat) : Type :=
  match n with
  | 0 => Unit
  | n + 1 => Nat × NProd n
```
Lastly, Lean makes it non-trivial to identify whether a function even has a type parameter by
unifying `Prop` and `Type u` in `Sort u`.

Instead of trying to encode all of these constructs into Nunchaku's logic, I will now define a
smaller fragment of Lean. This fragment will serve as the input for the reduction to Nunchaku.
The rationale for this is that, while all of these features are sometimes
useful, many Lean formalizations do not require them at all. Thus, handling a smaller fragment of
Lean can still yield a tool that is useful for many Lean users.

This fragment is akin to a "dependently typed @HOL" restriction of Lean. It supports only
rank 1 polymorphism, maintains a clearly decidable separation of types, values, propositions, and
proofs, and forbids type-producing functions. The consequence of these requirements for
the expression syntax is the need for a clear distinction between $"Prop"$ and $"Type" u$, given by the following
grammar:
$
Gamma & ::= Gamma, x : e | epsilon & "   " & "contexts" \
e &::= x | c | e " " e | lambda x : e . e | "let" x : e := e; e | (x : e) -> e | "Prop" | "Type" u & "   " & "expressions"
$
Given that this is a mere syntactic restriction of Lean's core calculus, we can reuse Lean's type
system with the typing judgment $Gamma tack e : e$.
In the following description of the further restrictions on the fragment, I will use $x, y, z$ to
denote variables; $alpha, beta, gamma$ to denote type expressions; $s, t, u$ to denote value
expressions; and $e$ to denote expressions that might be both. This convention for expressions carries no semantic meaning on its
own and is merely meant to aid in reading. However, the restrictions put on the expressions will enforce
a match between insinuated and actual meaning. When convenient, I will denote the dependent function type as
$forall x : alpha. t$ instead.

For constants, the fragment uses the previously introduced definitions and inductive types. To avoid
working with Lean's desugaring of recursive definitions, we will only consider definitions by
a list of equations, like Nunchaku. In practice these equations are automatically computed (and verified)
by Lean upon the declaration of a new definition.
#grid(
  columns: (1fr, 1fr),
  align: center,
$
& "def" c : alpha "where" \
& forall overline(x)_1 : overline(beta)_1. c " " overline(e)_1 = u_1 \
& dots.v \
& forall overline(x)_n : overline(beta)_n. c " " overline(e)_n = u_n \
$,
$
& "inductive" c " " (overline(x) : overline(alpha)) : beta "where" \
& "ctor"_1 : (overline(y)_1 : overline(gamma)_1) -> c " " overline(x) " " overline(t)_1 \
& dots.v \
& "ctor"_n : (overline(y)_n : overline(gamma)_n) -> c " " overline(x) " " overline(t)_n \
$
)
Observe that the type of an inductive is split into two parts: $(overline(x) : overline(alpha))$ and
$beta$. The $overline(x)$ part is called the _parameters_ of $c$ and remains fixed across all
constructors. If $beta$ contains additional arguments, they are called the _indices_ of $c$ and may vary across
constructors.

To impose the restriction of rank-1 polymorphism on this calculus, I use a notion of
monotypes $tack alpha "mono"$ and polytypes $tack alpha "poly"$, similar to Jones et al. @higherrankedspj.
Because types can depend on terms, defining them also requires a notion of monoterms $tack t "monot"$: 

#align(center, [
  #box(proof-tree(inf-rule(
    $tack c "mono"$,
    $c "is an inductive type"$,
  )))
  #box(proof-tree(inf-rule(
    $tack x "mono"$,
  )))
  #box(proof-tree(inf-rule(
    $tack "Prop" "mono"$,
  )))
  #box(proof-tree(inf-rule(
    $tack alpha " " beta "mono"$,
    $tack alpha "mono"$,
    $tack beta "mono"$,
  )))
  #box(proof-tree(inf-rule(
    $tack alpha " " t "mono"$,
    $tack alpha "mono"$,
    $tack t "monot"$,
  )))
  #box(proof-tree(inf-rule(
    $tack t " " alpha "monot"$,
    $tack t "monot"$,
    $tack alpha "mono"$,
  )))
  #box(proof-tree(inf-rule(
    $tack (x : alpha) -> beta "mono"$,
    $tack alpha "mono"$,
    $tack beta "mono"$,
  )))
  #box(proof-tree(inf-rule(
    $tack alpha "poly"$,
    $tack alpha "mono"$,
  )))
  #box(proof-tree(inf-rule(
    $tack (x : alpha) -> beta "poly"$,
    $tack alpha "mono"$,
    $tack beta "poly"$,
  )))
  #box(proof-tree(inf-rule(
    $tack (x : "Type" u) -> beta "poly"$,
    $tack beta "poly"$,
  )))
  #box(proof-tree(inf-rule(
    $tack c "monot"$,
    $c "is a def or ctor"$,
  )))
  #box(proof-tree(inf-rule(
    $tack x "monot"$,
  )))
  #box(proof-tree(inf-rule(
    $tack t " " u "monot"$,
    $tack t "monot"$,
    $tack u "monot"$,
  )))
  #box(proof-tree(inf-rule(
    $lambda x : alpha . t "monot"$,
    $tack alpha "mono"$,
    $tack t "monot"$,
  )))
  #box(proof-tree(inf-rule(
    $"let" x : alpha := t; u "monot"$,
    $tack alpha "mono"$,
    $tack t "monot"$,
    $tack u "monot"$,
  )))
])

Using these restrictions on terms and types, we can extend Lean’s usual constraints on constant
declarations to obtain the target fragment. First, the type $alpha$ of a definition must satisfy
$epsilon tack alpha : "Type" u$ and be a polytype; each equation $"eq"_i$ must likewise satisfy
$epsilon tack "eq"_i : "Prop"$ and also be a polytype.
Second, the overall type of an inductive $(overline(x) : overline(alpha)) -> beta$ must
satisfy $epsilon tack (overline(x) : overline(alpha)) -> beta : "Type" u$ and be a polytype, with the relaxation
that the rightmost arrow of $beta$ may produce a $"Type u"$. Furthermore, each constructor $"ctor"_i$ must
satisfy $epsilon tack (overline(x) : overline(a)) -> (overline(y)_i : overline(gamma)_i) -> c " " overline(x) " " overline(t)_i : alpha$
where $alpha$ is either $"Type" u$ or $"Prop"$, and must additionally satisfy $tack (overline(y)_i : overline(gamma)_i) -> c " " overline(x) " " overline(t)_i "mono"$
to rule out existential types. Finally, all index arguments $overline(t)_i$ appearing in the constructor’s target type must be monoterms.

In the remainder of this section I will describe the reduction from this restricted fragment
of Lean to the input logic of Nunchaku.

== Eliminating Dependent Types (8P) <sect_trans_dtt>
The first step of the reduction is the elimination of dependent types. Doing this before handling
polymorphism is not at all an obvious choice. In fact, as I am going to show, removing polymorphism
first and handling dependent types later might even yield a better reduction. The reason for
choosing to eliminate dependent types first despite this is simplicity. With this ordering only one step has to
deal with dependent types while the other way around both steps have to.

Dependent types generally occur in two flavors in the input fragment. First, a function or
inductive might take an argument that is a proof. This is an issue because Nunchaku has no notion of proof terms at
all so they need to be removed. Second, an inductive type may have term arguments.
If the inductive type lives in $"Prop"$, this is not an issue because Nunchaku's inductive
predicates work with term parameters. On the other hand, if the inductive lives in $"Type" u$
the term arguments need to be removed as well.

For handling proof terms we can make use of Lean's proof irrelevance. Because the concrete value of
a proof term cannot change the semantics of a program, they can be erased. This technique of _proof
erasure_ is a well established approach and is used by both the Lean code generator and the Rocq code
extractor @coqerasure already. The core idea is to introduce a new type $"Erased"$
with a single inhabitant $qed : "Erased"$. Then when a proof term needs to be removed we can replace
it with $qed$ and if a binder binds a proof we can replace the bound type with $"Erased"$.

- For the erasure of type dependency a further developed instance of the approach presented in the
  Nunchaku DTT paper @nunchakudtt in turn inspired by @dttold paper
  - given a dependent type separate it into two other types:
    - a non dependent type that carries around only the data required
    - a predicate over this non dependent type + the original value arguments that restraints them
      as to simulate the original dependent type
  - inject assumptions that this predicate must hold as necessary
  - important: This approach can only deal with value indices, not type indices
- The encoding proposed in @nunchakudtt has two crucial oversights:
  + The proposed invariant does not handle cases where types (whether they are dependent or not)
    contain other dependent types: Example with `Vec` specialized on `Fin 0` always being equal to
    `[]`
  + The proposed invariant does not handle types that are generic correctly: Example with
    `Vec (Fin 0) n` always being equal to `[]`
- To fix these:
  + While defining the invariant also take into account that the invariants for all other
    types that get bound in the constructor must hold
  + Generic types are a delayed obligation for an invariant that we will model by letting the
    invariant take a predicate for each of its generic types
- Present the invariant generation algorithm and the new inductive generation algorithm:
  - transformation on types
  - crucial: this algorithm is mutually recursive with the expression eliminator, already define its
    prototype and say we will define it later
- example with now correctly translated `Vec (Fin 0) n`
- move on to expression transformer:
  - key question: where to insert the invariants
  - answer: whenever a piece of data is bound by a universal quantifier
  - point out we already did this when generating the invariants
  - reason: Given that we are operating on a well typed problem all expressions that are being
    constructed do already fulfill the invariants. However, universal quantification opens the
    chance for Nunchaku to synthesize terms of the eliminated data type that do not fulfill the
    invariants. In order to prevent this we need to restrain those quantifiers.
- constant transformer:
  - inductive predicates
  - definitions
- optimization (put this into implementation if we don't have enough space): elimination of trivially true invariants:
  - refer back to the invariant generated for `Nat`
  - intuition: when an inductive type does not refer to a dependent type transitively its invariant
    is trivial and can be erased. Similarly if a function type does not produce such a type its
    invariant can be erased
  - show inference algorithm
- unsoundness with function extensionality:
  - fixable but likely to destroy performance

== Eliminating Polymorphism (4P) <sect_trans_poly>
- This leaves us in a non dependent fragment of Lean with "easy" polymorphism
  - $->$ in principle we could translate to Nunchaku right away and let it handle the rest
  - but: Lean's polymorphism is in principle much more expressive and I want to keep the opportunity
    to make this extension in the future
  - Recent work has been made in @monotypeflow towards extending monomorphization to higher ranked
    and existential polymorphism
  - $->$ implement this work for the rank 1 fragment in Lean to allow potential extensions in the
    future
  - nice bonus: Can determine solvability ahead of time
- exposition about type flow analysis
  - collect constraints on types like in data flow analysis
  - solve them using a fixpoint iterator
  - instantiate the solution to get a generics-free program
- show my type flow analysis
- talk about solvability
  - introduce new solvability check algorithm
- talk about how to apply the result

/*

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
In this section, I present two case studies that demonstrate Chako’s capabilities when applied to
realistic verification problems: bisection on arrays and AA trees. These examples were selected
to highlight the range of Lean constructs supported by Chako.

== Bisection <sect_case_studies_bisect>
The first example concerns the Lean standard library function `Array.binSearch`. It implements a
generic bisection algorithm for sorted arrays.
```lean
def binSearchAux {α : Type u} (lt : α → α → Bool) (as : Array α) (k : α)
    (lo : Fin (as.size + 1)) (hi : Fin as.size) (h : lo.1 ≤ hi.1) :
    Option α :=
  let m := (lo.1 + hi.1) / 2
  let a := as[m]
  if lt a k then
    if h' : m + 1 ≤ hi.1 then
      binSearchAux lt as k ⟨m + 1, by grind⟩ hi h'
    else
      none
  else if lt k a then
    if h' : m = 0 ∨ m - 1 < lo.1 then
      none
    else
      binSearchAux lt as k lo ⟨m - 1, by grind⟩ (by grind)
  else
    some a
termination_by hi.1 - lo.1

def binSearch {α : Type u} (as : Array α) (k : α) (lt : α → α → Bool) :
    Option α :=
  let lo := 0
  let hi := as.size - 1
  if h : lo < as.size then
    binSearchAux lt as k ⟨lo, by grind⟩ ⟨hi, by grind⟩ (by grind)
  else
    none
```
While the algorithmic side is quite simple, this program already suffices to demonstrate quite a few of the
features supported by Chako. First, the implementation is generic over the type of elements of the
array, calling the monomorphizer into action. Second, `binSearchAux` makes use of well-founded
recursion, carries an explicit proof argument `h`, and works with the dependent type `Fin` to avoid
bounds checks.
#pagebreak(weak: true)
Let us first consider a completeness theorem for `Array.binSearch`. The formulation uses the
proof-carrying type class `TotalOrder` to constrain the $<$ relation on `α`:
```lean
theorem complete [TotalOrder α] [DecidableLT α] (xs : Array α)
    (h : n ∈ xs) : xs.binSearch n (· < ·) = some n
```
Chako produces a counterexample in $0.2$ seconds, but it synthesizes a quite unreadable $<$
on `α`, which makes the counterexample difficult to interpret. Instead of checking this fully
general theorem, we can inspect a version specialized on `Nat` to get a more understandable output:
```lean
theorem complete (xs : Array Nat) (h : n ∈ xs) :
    xs.binSearch n (· < ·) = some n
```
For this version, Chako finds the counterexample `xs := #[1, 0]` and `n := 0`, which allows us to pinpoint the flaw in
this specification: `xs` is not restricted to sorted arrays. After adding this additional
assumption, Chako times out as expected.

In addition to completeness, we might also be interested in verifying soundness:
```lean
theorem sound (xs : Array Nat) :
    xs.binSearch n (· < ·) = some y ↔ n = y
```
Note that this theorem should hold even for unsorted arrays; if the function returns a value,
it should be the one we were looking for. However, the current statement does not capture this idea
correctly. Chako reveals the issue with the counterexample `n := 0`, `y := 0`, and `xs := #[]`.
The problem is that the theorem is stated too strongly, using `↔` instead of `→`.

== AA Trees <sect_case_studies_aa>
The second case study is an AA tree @aatrees formalization. AA trees are self-balancing search
trees designed with a focus on simple implementation. I selected this example for two reasons.
First, it involves a tree-shaped data structure and a non-trivial invariant, both things that are
not covered by the bisection example. Second, Nunchaku has a test called `slow_aa_trees`, derived from the Nitpick
case study on AA trees @nitpickpred, which heavily inspired this case study. This Nunchaku test case
remained unsolved (within a reasonable time) by Nunchaku until the improvements described in @sect_impl_nunchaku.

The foundation of this case study are the AA tree itself and some utility functions:

```lean
inductive AATree (α : Type u) where
  | nil
  | node (x : α) (level : Nat) (l r : AATree α)
```
#grid(
  columns: (1fr, 1fr),
```lean
def left : AATree α → AATree α
  | nil => .nil
  | node _ _ l _ => l
```,
```lean
def right : AATree α → AATree α
  | nil => .nil
  | node _ _ _ r => r
```
)

#grid(
  columns: (1fr, 1fr),
```lean
def lvl : AATree α → Nat
  | nil => 0
  | node _ lvl _ _ => lvl
```,
```lean
def isNil : AATree α → Bool
  | nil => true
  | node .. => false
```
)

```lean
def data (t : AATree α) (h : t.isNil = false := by grind) : α :=
  match t with
  | nil => False.elim (by grind [isNil])
  | node x .. => x

def mem (x : α) : AATree α → Prop
  | nil => False
  | node d _ l r => d = x ∨ mem x l ∨ mem x r
```

The self-balancing mechanism of AA trees revolves around maintaining the following invariant on the
level field of the nodes:
1. Nil nodes have level $0$
2. Leaf nodes have level $1$
3. A node's level must be $>=$ its right child's and $>$ than its left child's
4. Every node of level $> 1$ must have two non-nil children

This invariant can be almost directly expressed in Lean like so:
```lean
def WF : AATree α → Prop
  | nil => True -- nil has level 0 by definition
  | node _ lvl nil nil => lvl = 1
  | node _ lvl l r =>
    WF l ∧ WF r ∧
    lvl ≥ r.lvl ∧ lvl > l.lvl ∧ (lvl > 1 → (!l.isNil ∧ !r.isNil))
```
For performing the actual rebalancing operation, AA trees use two auxiliary functions called `skew` and `split`:
```lean
def skew : AATree α → AATree α
  | nil => nil
  | node x lvl l r =>
    if h : !l.isNil ∧ lvl = l.lvl then
      node l.data lvl l.left (node x lvl l.right r)
    else
      node x lvl l r

def split : AATree α → AATree α
  | nil => nil
  | node x lvl l r =>
    if h : !r.isNil ∧ lvl = r.right.lvl then
      node r.data (lvl + 1) (node x lvl l r.left) r.right
    else
      node x lvl l r
```
Both of these functions have some interesting properties with respect to the `mem` and `WF`
predicates:
#grid(
  columns: (1fr, 1fr),
  rows: (auto, auto),
  row-gutter: 2em,
  align: center,
```lean
mem x t ↔ t.skew.mem x
```,
```lean
mem x t ↔ t.split.mem x
```,
```lean
WF t → t.skew = t
```,
```lean
WF t → t.split = t
```
)
For the well-formedness properties, Chako (correctly) times out. For the membership ones,
Nunchaku's solvers report (also correctly) that they are generally true. Although Chako does not
provide a way to recover these proofs into Lean, this still provides the user reassurance during development.

With these auxiliary functions in place, the insertion operation can be defined almost exactly as
it is for primitive binary search trees:
```lean
def insert [LT α] [DecidableLT α] (t : AATree α) (x : α) : AATree α :=
  match t with
  | nil => .node x 1 nil nil
  | node y lvl l r =>
    let l' := if x < y then l.insert x else l
    let r' := if x > y then r.insert x else r
    split <| skew <| node y lvl l' r'
```
In order to keep the tree balanced, the `insert` function must preserve the `WF` invariant:
```lean
theorem WF_insert [TotalOrder α] [DecidableLT α] (t : AATree α) :
    WF t → WF (t.insert x)
```
Indeed Chako finds no counterexample for this within its default timeout.

Let us now introduce a suble bug into the implementation and observe how Chako fairs at detecting it:
#footnote[This bug is a typo that I unintentionally made during the initial implementation of this
case study]
```diff
 def skew : AATree α → AATree α
   | nil => nil
   | node x lvl l r =>
-    if h : !l.isNil ∧ lvl = l.lvl then
+    if h : !l.isNil ∧ lvl = r.lvl then
       node l.data lvl l.left (node x lvl l.right r)
     else
       node x lvl l r
```
As in the bisection example, Chako is configured to search for `AATree Nat` counterexamples to keep the
output readable. In this configuration, Chako quickly reports the counterexample `t := node 1 0 nil nil` and `x := 0`.
To confirm the bug, we can run the broken `insert` operation with the counterexample, which yields
`node 1 1 (node 0 1 nil nil) nil`. This tree violates condition 3 of the invariant, since the level of
the root node is not greater than its left child's.

TODO: If the chance arises it would be great to have a third case study about inductive predicates

#pagebreak(weak: true)

= Evaluation (2-3P) <sect_eval>
- This section aims at 2 things:
  + Demonstrate that, despite the lack of proof and the known issues with the encoding Chako is at
    least empirically sound most of the time
  + Demonstrate its performance on a larger scale data set by evaluating it on the theories from
    stdlib
- For soundness:
  - run Chako on theorems from stdlib with its default timeout and see if we get any SAT
  - show data
  - blame SAT on Kodkod encoding
- For performance:
  - take same theorems from stdlib and mutate them:
    - replacing certain constants
    - typoing free variables
    - dropping assumption
    - crucial: any of these activities may produce ill typed theorems due to dependent types so we
      only allow those mutants in that pass a type check
  - present data
  - explain results:
    - UNSAT is because some theorems remain true even when mutated (give a few examples)
    - large amount of encoding errors in `Array` is because the higher order functions of `Array`
      are first defined as generic monadic ones and then specialized on the `Id` monad for their
      pure variants $->$ higher kinded type polymorphism $->$ not possible at the moment
  - cactus plot?
- If too much space: ablation study with taking away solvers

#pagebreak(weak: true)
= Outlook (1P) <sect_outlook>
Things for future work:
- extending the fragment of Lean that is supported:
  - allowing for type producing functions
  - allowing for higher kinded / higher ranked / existential polymorphism
- maybe experiment eliminating the other way around, this would in particular resolve:
  - function extensionality
  - make problems with generic types easier to generate invariants for
- Further optimizing the problems Nunchaku generates for solvers as well as finding and fixing more
  bugs in the pipeline

#v(15pt)
#[Total characters counted excluding code blocks: #total-characters] <no-wc>
