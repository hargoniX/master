#import "./template.typ": *

#show: notes.with(
  title: "Master Thesis Notes"
)

#let val = $bold("val")$
#let axiom = $bold("axiom")$
#let spec = $bold("spec")$
#let band = $bold("and")$
#let rec = $bold("rec")$
#let data = $bold("data")$
#let def = $bold("def")$
#let pred = $bold("pred")$
#let copy = $bold("copy")$
#let goal = $bold("goal")$
#let abstract = $bold("abstract")$
#let concrete = $bold("concrete")$
#let nunsubset = $bold("subset")$
#let quotient = $bold("quotient")$
#let partialquotient = $bold("partial_quotient")$
#let fun = $bold("fun")$
#let nunlet = $bold("let")$
#let nunif = $bold("if")$
#let nunthen = $bold("then")$
#let nunelse = $bold("else")$
#let asserting = $bold("asserting")$
#let match = $bold("match")$
#let nunforall = $bold("forall")$
#let nunexists = $bold("exists")$
#let nunpi = $bold("pi")$
#let prop = $bold("prop")$
#let type = $bold("type")$
#let nunnot = $not$
#let nunand = $and$
#let nunor = $or$
#let nuntrue = $top$
#let nunfalse = $bot$
#let nuneq = $=$
#let nunequiv = $<=>$
#let nunimply = $=>$

= Existing Pipeline to CVC4
TODO: understand the traversal framework better


We started in the basic, not necessarily type ascribed representation.
$
  "copy_wrt" &:= nunsubset "term"  \
             &| quotient "term" \
             &| partialquotient "term" \
  "stmt" &:= val "id" : "term" & "an axiomatic value" \
         &| axiom "term" & "an axiomatic property" \
         &| spec ("id" : "term") [band ("id" : "term")]^* :=  ["term";]^+ & "specifying symbols with associated laws" \
         &| rec ("id" : "term") := ["term";]^+ [band ("id" : "term") := ["term";]^+]^* & "mutually recursive functions" \
         &| data "id" ["id"]^* := [ | "id" ["term"]]^+ [band "id" ["id"]^* := | "id" ["term"]]^* & "mutually inductive data types" \
         &| def "id" := "term" & "simple aliasing definition" \
         &| pred "id" : "term" := ["term";]^+ ["and" "id" : "term" := ["term";]^+]^* & "mutually inductive predicate" \
         &| copy "id" ["id"]^* := "term" ["copy_wrt"]? abstract "id" concrete "id"  & "copy type"\
         &| goal "term" & "the goal of this nunchaku invocation" \
  "typed_var" &:= "id" \
              &| ("id" : "term") \
  "term" &:= "id" & "variable" \
         &| "term" " " "term" & "application" \
         &| fun "typed_var"^+ " . " "term" & "lambda abstraction" \
         &| nunlet "id" := "term" bold("in") "term" & "let abstraction" \
         &| match "term" bold("with") [ | "term" -> "term"]^+ bold("end") & "pattern matching" \
         &| nunif "term" nunthen "term" nunelse "term" & "if-then-else" \
         &| nunforall "typed_var"^+ " . " "term" & "logical universal quantifiaction" \
         &| nunexists "typed_var"^+ " . " "term" & "logical existential quantifiaction" \
         &| "term" -> "term" & "function arrow" \
         &| nunpi "typed_var"^+ " . " "term" & "type universal quantifiaction" \
         &| "term" asserting "term" & "term guard construct" \
         &| prop & "universe of propositions" \
         &| type & "universe of types" \
         &| nunnot & "logical not" \
         &| nunand & "logical and" \
         &| nunor & "logical or" \
         &| nuntrue & "logical true" \
         &| nunfalse & "logical false" \
         &| nuneq & "value equality" \
         &| nunequiv & "logical inequality" \
         &| nunimply & "logical implication" \
$

== Type Inference
In this step we perform type inference and checking, in particular:
- the term of $axiom$ gets annotated and enforced to be a proposition
- the terms of $spec$ gets annotated and we reduce to a more uniform representation where $spec$ is
  just a special kind of axiom
- similarly with $rec$
- $def$ gets erased and processed the same way that $rec$ does
- terms in $data$ and $pred$ get annotated, furthermore we ensure they have proper constructors etc.
- terms in $copy$ get annotated and the condition as well as conversion functions get type checked
- term in $goal$ gets annotated and enforced to be a proposition.

In particular it is enforced that:
- terms cannot contain universal type quantification so things like axioms or goals can at most have existential type quantification.
- all types must be in prenex normal form (IMPORTANT: This can make some of DTT difficult)

Terms get reduced in a fashion where now:
- every variable is annotated with its typed
- names referring to constants are singled out but not annotated
- all kinds of binders have their new variables' type annotated

This allows us to perform local type inferences and quite a few semantic
analyses as very syntactical algorithms.

== Skolemization
In this phase we run type skolemization, that is we look for
existential quantifiers in positive polarity or universal quantifiers over types
in negative polarity over things of kind $bold("type")$ and replace them
with fresh skolem symbols.

The polarity of a term is determined by how many negations are along the traversal from the root
towards it.

This step removes all type variables that would have been existentially quantified in a prenex
normal form world. This leaves type variables in universally quantified positions.

== Monomorphization
In this phase we run monomorphization for type arguments. For this we look for call sites of
functions with type arguments and parametric types and create clones of them with the specific type
arguments at their call sites inlined.

Note that this pass only works because we forbid universal type quantification (or existential one
in negative polarity) in things like axioms and goals so it is guaranteed, that the leafs of our
dependency graph are always using concrete types (this includes of course, such types that are bound
via $val$).

This step should remove the last bits of type quantification and ensure that we are now in a fully
monomorphic representation without any generic types.

== Elimination of Infinite Types
This pass attempts to eliminate types that have the `[infinite]` attribute. This is done by
either introducing an approximation type or using an already defined one tagged with `[approx_of ty]`,
usually together with a function $"upcast" : "approx_ty" -> "orig_ty"$ tagged with `[upcast]`.
This is done by dropping the infinite type and replacing it with the approximation one and, if an
upcast function is declared, removing that as well as it will have become the identity function. The
crucial contribution of this pass is to detect when we are in situations that quantify over infinite
types as we loose completeness (i.e. UNSAT from our solver in the end is now equal to UNKNOWN).

This pass currently lacks the ability to decode again.

== Elimination of Copy Types
This pass gets rid of the $copy$ type mechanism. Generally speaking a copy type $tau'$ is some base type
$tau$ together with some additional constraint. Currently these constraints can be:
- no constraint
- a so called subset constraint where some property $p : tau -> prop$ holds
- a partial or total quotient with respect to some relation $r : tau -> tau -> prop$

Furthermore each $copy$ type postulates:
- an abstraction function $alpha : tau -> tau'$
- a concretization function $gamma : tau' -> tau$

The elimination of $tau'$ case splits on the kind of constraint:
- for no constraint we declare an inductive type $tau'$ with a constructor $alpha : tau -> tau'$ and
  a function $gamma : tau' -> tau$ that pattern matches on this single constructor and returns the
  contained value
- for $"subset"$ we first determine whether the type is "complete" we do this by performing an
  analysis of the cardinality of $tau$. If we can determine a precise cardinality and we deem it to
  be sufficiently small (currently $<= 4$) we say the type is complete, otherwise incomplete:
  - declare an uninterpreted type $tau'$ with:
    - attribute `[incomplete]` if the type is incomplete
    - attribute `[max_card_hint n]` where $n$ is the cardinality of $tau$
  - declare uninterpreted functions $alpha : tau -> tau'$ and $gamma : tau' -> tau$
  - add at least the following axioms:
    - $forall (a : tau'), alpha(gamma(a)) = a$
    - $forall (a : tau'), p(gamma(a))$
  - if the type is complete add the axioms:
    - $forall (c : tau), p(c) => c = gamma(alpha(c))$
- for $"quotient"$ we take the same approach as with subset but add slightly different axioms:
  - at least the following ones:
    - $forall (a : tau'), alpha(gamma(a)) = a$
    - $forall (a : tau'), p(gamma(a), gamma(a))$
    - $forall (a " " b : tau'), p(gamma(a), gamma(a)) => a = b$
  - if the type is complete:
    - $forall (c : tau), p(c, c) => p(c, gamma(alpha(c))) $ if the quotient is partial
    - $forall (c : tau), p(c, gamma(alpha(c)))$ if the quotient is total

TODO:
- effect of `incomplete` and `max_card_hint` attributes
- describe cardinality analysis
- think about what a partial quotient means, maybe that the property is not necessarily reflexive?
- think about why the axiomatizations suffice

== Elimination of Multi Equations
This pass turns recursive definitions using equations into a single lambda that uses
nested pattern matching constructs to encode the equations

TODO: answer by Simon as to whether there is a paper for this kind of algorithm

After this pass every definition only consists of a single equation, these single equations use
multiple nested `match` invocations to realize the control flow. Furthermore pattern matches are not
able to match directly, e.g. to match `Suc (Suc n)` we need two successive `match`.

== Specialisation
If there are functions or predicates with static arguments (i.e. arguments that are passed unchanged to all
recursive calls) we generate clones of those functions with these arguments removed. This may in
particular apply to higher order functions that occur in constructs like `map`.

First half of the file performs a more or less global call graph analysis in hopes of finding
specialisation opportunities. Second half of the file is concerned with inserting those
opportunities as specialisations based on some heuristic (`decide_if_specialize`).

Finally we need to add congruence axioms in certain situations. In particular two kinds

1. for non deterministic functions that get specialised with axioms that have closure variables
   we need self congruence axioms. For instance, specializing `choice (fun x. f x y)`
   should create `choice42 y`, with the axiom `forall y1 y2. (fun x. f x y1)=(fun x. f x y2) => choice42 y1=choice42 y2`
2. the various specialisations of a function form a lattice ordered by generality $f("args1") < f("args2") <-> exists sigma. sigma("args2") = "args1"$
   according to this graph we add axioms that ensure the more concrete versions agree with the less
   concrete ones on all inputs. This is done using the lattice approach to avoid an $n!$ style
   blowup.

Note that if the functions are total (which they always are in Lean!) we will be able to avoid
generating these equations. The point is that for inputs on which they are undefined the models
needs to agree, but if the functions are defined on all inputs there is no need for this.

== Constructor as Function
This pass ensures that all constructor applications are full and no partial one is left.
This is achieved by looking for partial constructor applications (as well as constructors just
floating around without any arguments (apart from of course 0-ary constructors)) and if they occur
generate a new function that just calls the full constructor (note that this only generates one
function per constructor, no specialisation etc. maybe it could be of interest to have this in the
future?) and applying it there. These functions are of course reused.

After this pass every constructor application if full, according to the docstring of `cstor_as_fun`
this is important as we can't add guards on it otherwise.

== Match Elimination
This pass eliminates both data and codata pattern matches, this is done by inspecting an individual
`match` and turning it into a sequence of if-then-else. To do this for each constructor $c : x_0 ->
x_1 -> ... -> x_n -> tau$ of each inductive type $tau$ we add:
- $"is-c" : tau -> prop$
- for each $x_0, x_1, ..., x_n$ we add $"select-c-i" : tau -> tau_x_i$

then to pattern match on some term $t$ we instead check $"is-c"(t)$ and go into the appropriate arm.
Within this arm we substitute the pattern variables $x_1, ..., x_n$ with $"select-c-i"(t)$.

After this pass the `match` construct is fully gone.

== Polarization
== Unrolling
== Skolemization
== Inductive Predicated Elimination
== Lambda Lifting
== Higher Order Function Elimination
== Recursion Elimination
== Guard Introduction
== Model CLeaning
== First Order Conversion
== CVC4 Reduction

= Translation
Facts:
- base idea: https://inria.hal.science/hal-01401696/document
- Additional Axioms:
  - proof irrelevance and propext:
    - dropping proof terms
    - things like casting along an equality
  - function extensionality
- crucial mechanism: `asserting`, $t "ASSERTING" phi equiv "IF" phi "then" t "ELSE" bot$

Questions:
- what is a polarized context?
- How do we deal with universe polymorphism when translating sorts? `Prop` and `Type` are quite
  different after all
- How do we deal with projections?
- How do we deal with pi types?
- How to apply the `Expr` translation recursively?
  - I think we have to go outside in?
- how to `let`?
  - interesting sub question: do we try to lambda lift?
- How do we deal with the fact that nunchaku assumes every type is inhabited?
  - Idea: For "obviously" (certain definition) empty types add an axiom that allows us to prove
    false?
- how to deal with type class arguments? paper has some (not really fleshed out ideas)
- Performance question: reducing structurally recursive functions to recursors or using equations?
- Think through recursor translation
- How to deal with type alias definitions, can hopefullly be done using the standard "just drop the
  term arguments" approach?
- How to compute invariants of non specialised dependent type arguments
- Low prio: Quotients? Maybe copy types? They seem to have quotients
- Low prio: Subtypes and structures with only additional properties? Maybe subset copy types?


== Approach
Basic idea: erase dependent parameters from types and insert additional predicates to enforce
constraints that these dependent parameters would have otherwise enforced.

In the following we consider a dependent type $tau$ with type arguments $overline(u)$ and term arguments
$overline(t)$. We denote the erased version of $tau$ with $tau'$ and its associated predicate with
$"inv"_tau$.

=== Expr

How do we translate `Lean.Expr`, we assume mvar free:
- variables -> nunchaku variables
- sort -> to `type` or `prop` depending on level?
- const -> nunchaku constants
- app -> nunchaku app
- lit -> nunchaku lits
  - -> maybe have to always introduce `Nat` and `String`?
- mdata -> drop
- proj -> ??
- lambdas: $lambda (x : tau " " overline(t) " " overline(u)), v$ becomes $lambda (x : tau' " "
  overline(u), (v "ASSERTING" "inv"_tau " " overline(t) " " x))$
- dep forall (propositional): $forall (x : tau " " overline(t) " " overline(u)), phi$ becomes $forall (x : tau' " "
  overline(u), "inv"_tau " " overline(t) " " x => phi)$
- dep forall (pi types) -> ??
- indep forall (propositional) -> implication nunchaku
- indep forall (pi types) -> nunchaku function arrow
- let -> ??

A couple of notably complicated constructions:
- `Eq`:
  - `h : x = y` should probably be translated to nunchaku built-in equality
  - casting along an `Eq`: `Eq.rec h x` could be translated as $("cast " x) "ASSERTING" h$ where
    - `cast` is able to do arbitrary type conversions
    - should be droppable after sufficient monomorphization as it should have been turned into an
      `id` function by then
  - different kinds of equality possible:
    - equality of values -> encode to built-in nunchaku equality
    - equality of propositions -> encode to iff and only iff (assumes `propext`)
    - equality of types -> in our erased world these types should always be equal so can probably
      encode to `true`?
- `Quot`: low prio problem
- `HEq`: probably don't bother
- handling empty types? `False`, `Empty`
- handling basic logical connectives: `And`, `Not`, `Or`, etc -> translate to nunchaku built-ins?
  - `Exists` probably needs to be handled like dep forall
- dealing with type class arguments ??
- investigate how `pred` in nunchaku works and how we can map prop valued inductives to it
- will probably assume Type in Type for first approach

=== Definitions
We have:
- `axiom`: Translating the proposition and then turning it into a nunchaku axiom
  - potentially interesting: translating anything beyond the built-in axioms could require $O(n)$
    environment iteration, keep an index of declared axioms somewhere?
- `opaque`: translate like axiom?
- `def`:
  - Nonrecursive definitions eliminating into values can probably just be translated directly using
    the term reduction
  - Recursive definitions eliminating into values have to handle two cases:
    1. structural recursion: Is in principle based on recursors and _could_ thus be translated quite
       naively by using the translated recursors, I don't know whether this is a good idea over
       translating to equations though -> evaluate
    2. well founded recursion: Translate to equations based on the generated recursive equations
    Note: No type polymorphic recursion is supported, we should catch this on the Lean side if
    possible.
  - Any non-aliasing type definition is probably doomed
  - Aliasing type definitions ???
  - nested matches?
- `theorem`: should never have to be translated but can basically be treated the same as `axiom` as
  we know its provable and can thus just drop the body
- `inductive`:
  - `Type` valued inductives, the paper "only" supports inductive types with:
     - term parameters and indices
     - type parameters
     so no GADTs, for this fragment the approach is to just remove all term parameters and indices and
     keep the type ones.
  - `Prop` valued inductives a bit unclear, check `pred` in nunchaku
- `recursor`: reduction to pattern matching possible but could be quite complicated if sufficiently
  complicated dep types are around, think this through

In general interesting questions: What do we do with universe polymorphic stuff? Monomorphize
everything? Provide two copies of everything?

=== Computing Dependent Type Invariants
We have:
- `inductive` types: paper describes approach but we basically generate a recursive predicate
- type aliases: try to get invariant of the lias
- dependent type arguments, e.g. `(b : Nat -> Type) -> (x : Nat) -> ((a : Nat) -> b a) -> b x`:
  - can't determine at the beginning of the translation yet
  - observation: could determine after specialisation
  - observation: if it stays generic no chance
  - idea: add an "early specializiation pass" to kill these if possible


= Evaluation
Facts:
- apparently `logitest` was replaced with https://github.com/sneeuwballen/benchpress
- problems in https://github.com/nunchaku-inria/nunchaku-problems/

Questions:
- how to use nunchaku-problems? Port to benchpress? -> Simon
- how to integrate -> CI?


= CVC5
Facts:
- Files:
  - `backends/CVC4.ml`
  - `main/nunchaku.ml`

Questions:
- Just drop CVC4 and replace with CVC5 or keep both? -> Simon
- Investigate `ElimPatternMatch` and `ElimRecursion`:
  - What do they do?
  - Are they necessary with CVC5?
- Check SMT-LIB format
  - Do we want to serialize differently to CVC5?
  - Do we need to parse the model differently?
- What options to pass to CVC5? Different from CVC4?

= Writing
- Title: ?
- Structure:
  + System Description Nunchaku
    + Input Syntax
    + More or less detailed description of the reductions
    + Talk about solver specific stuff?
  + Integrating Lean with Nunchaku
    + Explain Reduction
  + Evaluation
    + Multi Solver
    + Which data set?
