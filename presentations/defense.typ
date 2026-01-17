#import "theme.typ": *
#import "@preview/cetz:0.4.1"
#import "@preview/fletcher:0.5.8" as fletcher: node, edge
#import "generated.typ": *

#let target_date = datetime(year: 2026, month: 1, day: 22)
#let fletcher-diagram = touying-reducer.with(reduce: fletcher.diagram, cover: fletcher.hide)

#show: lmu-theme.with(
  aspect-ratio: "16-9",
  footer: self => self.info.author,
  header-right: none,
  footer-progress: false,
  config-info(
    // TODO
    title: [Finite Model Finding for Lean 4],
    subtitle: [Thesis Defense],
    author: [Henrik Böving],
    date: target_date.display("[day].[month].[year]"),
    institution: text(14pt, smallcaps("Ludwig-Maximilians-Universität München")),
    logo: image("lmu-sigillium.svg", height: 25%),
  ),
)
#show link: set text(fill: blue.darken(20%))

#title-slide()

= Motivation
- People make mistakes while specifying complex systems or stating theorems
- Figuring out that you are trying to prove a false theorem takes time
- $->$ use automated counter example generation to avoid wasting that time
- Two very successful tools in Isabelle:
  - random testing (`quickcheck`) $->$ `plausible` in Lean 4
  - finite model finding (`nitpick`) $->$ ? in Lean 4

= Nitpick Architecture
#align(center, fletcher-diagram(
  node-stroke: none,
  node-fill: none,
  spacing: 6em,
  edge-stroke: 2pt,
  {
    node((0,0), text(size: 30pt)[Isabelle/HOL])
    node((1,0), text(size: 30pt)[Nitpick])
    node((2,0), text(size: 30pt)[Kodkod])

    edge((0,0), (1,0), "->", stroke: 2pt, bend: 0deg)
    edge((1,0), (2,0), "->", stroke: 2pt, bend: 0deg)
  }
))


= Nunchaku Vision
#align(center, fletcher-diagram(
  node-stroke: none,
  node-fill: none,
  spacing: 6em,
  edge-stroke: 2pt,
  {
    node((0,0), text(size: 30pt)[Prover $alpha$])
    node((0,1), text(size: 30pt)[Isabelle/HOL])
    node((0,2), text(size: 30pt)[Prover $beta$])

    node((1,1), text(size: 30pt)[Nunchaku])

    node((2,0), text(size: 30pt)[Solver $delta$])
    node((2,1), text(size: 30pt)[Kodkod])
    node((2,2), text(size: 30pt)[Solver $gamma$])

    edge((0,0), (1,1), "->", stroke: 2pt, bend: 0deg)
    edge((0,1), (1,1), "->", stroke: 2pt, bend: 0deg)
    edge((0,2), (1,1), "->", stroke: 2pt, bend: 0deg)

    edge((1,1), (2,0), "->", stroke: 2pt, bend: 0deg)
    edge((1,1), (2,1), "->", stroke: 2pt, bend: 0deg)
    edge((1,1), (2,2), "->", stroke: 2pt, bend: 0deg)
  }
))

= Nunchaku At The Start
#align(center, fletcher-diagram(
  node-stroke: none,
  node-fill: none,
  spacing: 4em,
  edge-stroke: 2pt,
  {
    node((0,1.5), text(size: 30pt)[Isabelle/HOL])

    node((1.0,1.5), text(size: 30pt)[Nunchaku])

    node((2,0), text(size: 30pt)[CVC4])
    node((2,1), text(size: 30pt)[Kodkod])
    node((2,2), text(size: 30pt)[Paradox])
    node((2,3), text(size: 30pt)[SMBC])

    edge((0,1.5), (1,1.5), "->", stroke: 2pt, bend: 0deg)

    edge((1,1.5), (2,0), "->", stroke: 2pt, bend: 0deg)
    edge((1,1.5), (2,1), "->", stroke: 2pt, bend: 0deg)
    edge((1,1.5), (2,2), "->", stroke: 2pt, bend: 0deg)
    edge((1,1.5), (2,3), "->", stroke: 2pt, bend: 0deg)
  }
))

= Nunchaku Now
#align(center, fletcher-diagram(
  node-stroke: none,
  node-fill: none,
  spacing: 4em,
  edge-stroke: 2pt,
  {
    node((0,1), text(size: 30pt)[#text(blue)[Lean 4]])
    node((0,2), text(size: 30pt)[Isabelle/HOL])

    node((1.0,1.5), text(size: 30pt)[#text(blue)[Nunchaku]])

    node((2,0), text(size: 30pt)[#text(blue)[cvc5]])
    node((2,1), text(size: 30pt)[Kodkod])
    node((2,2), text(size: 30pt)[Paradox])
    node((2,3), text(size: 30pt)[SMBC])

    edge((0,1), (1,1.5), "->", stroke: 2pt, bend: 0deg)
    edge((0,2), (1,1.5), "->", stroke: 2pt, bend: 0deg)

    edge((1,1.5), (2,0), "->", stroke: 2pt, bend: 0deg)
    edge((1,1.5), (2,1), "->", stroke: 2pt, bend: 0deg)
    edge((1,1.5), (2,2), "->", stroke: 2pt, bend: 0deg)
    edge((1,1.5), (2,3), "->", stroke: 2pt, bend: 0deg)
  }
))

= Lean to Nunchaku
Chakos' pipeline:
+ Preprocessing
+ Dependent Type Elimination
+ Polymorphism Elimination
+ Nunchaku Encoding

= Dependent Type Elimination
Basic idea from Cruanes and Blanchette:
- split dependent types into two:
  - non-dependent data type
  - invariant predicate relating data and indices
- use non-dependent data type for quantifiers
- insert invariant predicate as required

= Example

```lean
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons (x : α) (xs : Vec α n) : Vec α (n + 1)
```

```lean
inductive Data (α : Type) : Type where
  | nil : Data α
  | cons (x : α) (xs : Data α) : Data α
```

```lean
inductive Inv (α : Type) : Nat → Data α → Prop where
  | nil : Inv α 0 .nil
  | cons (x : α) (xs : Data α) (h : Inv α n xs) : Inv α (n + 1) (.cons x xs)
```

= Handling Polymorphic Inductives Correctly

```lean
inductive Inv (α : Type) (p : α → Prop) : Nat → Data α → Prop where
  | nil : Inv α p 0 .nil
  | cons (x : α) (h1 : p x) (xs : Data α) (h2 : Inv α p n xs)
    : Inv α p (n + 1) (.cons x xs)
```

`Vec (Vec Nat n) n` has the invariant `Inv (Data Nat) (Inv Nat NatInv n) n`

= Eliminating Polymorphism
Requirements:
- Only needs to handle rank-1 for now
- Extensible to other kinds of polymorphism in the future

#pause

#quote(attribution: [Eisenberg and Peyton Jones], block: true,
  [Higher-rank types cannot be monomorphized at all.]
)

#pause

#quote(attribution: [Lutze et al.], block: true,
  [We present a novel understanding of monomorphization, which is not only
easy to understand but also generalizes to higher-rank and existential polymorphism.]
)

= Type Flow Analysis
Like data flow analysis but with types:
+ Collect constraints based on the program
+ Use a fixpoint solver to find a solution
+ Instantiate the solution to get a monomorphic program

= Example: Collecting

#align(center, fletcher-diagram(
  node-stroke: none,
  node-fill: none,
  spacing: 4em,
  edge-stroke: 2pt,
  {
    node((0,0), [
```lean
inductive List (α : Type) where
  | nil
  | cons (x : α) (xs : List α)

def length (β : Type) (xs : List β) :=
  match xs with
  | .nil => 0
  | .cons _ xs => length β xs + 1

length Nat xs + length String ys
```
    ])

 node((2,0), [
$
  "Nat" &subset.eq.sq beta \
  "String" &subset.eq.sq beta \
  beta &subset.eq.sq alpha \
  beta &subset.eq.sq beta \
  alpha &subset.eq.sq alpha \
$
    ])

    edge((0,-0.05), (2,-0.05), "->", stroke: 2pt, bend: 0deg)
}))


= Example: Solving
#align(center, fletcher-diagram(
  node-stroke: none,
  node-fill: none,
  spacing: 4em,
  edge-stroke: 2pt,
  {
    node((0,0), [
$
  "Nat" &subset.eq.sq beta \
  "String" &subset.eq.sq beta \
  beta &subset.eq.sq alpha \
  beta &subset.eq.sq beta \
  alpha &subset.eq.sq alpha \
$])

    node((2,0), [
$
  beta &= beta union {"Nat"} \
  beta &= beta union {"String"} \
  alpha &= alpha union beta \
  beta &= beta union beta \
  alpha &= alpha union alpha \
$])

    node((3.5, 0), [
      $
        alpha &|-> {"Nat", "String"} \
        beta &|-> {"Nat", "String"} \
      $
    ])

    edge((0,0), (2,0), "->", stroke: 2pt, bend: 0deg)
    edge((2,0), (3.5,0), "->", stroke: 2pt, bend: 0deg)
  }
))

= Example: Instantiating

$ { alpha |-> {"Nat", "String"}, beta |-> {"Nat", "String"}} $

#grid(
  columns: (1fr, 1fr),
  align: center,
```lean
inductive ListN : Type where
  | nil
  | cons (x : Nat) (xs : ListN)

def lengthN (xs : ListN) :=
  match xs with
  | .nil => 0
  | .cons  xs => lengthN xs + 1
```,
```lean
inductive ListS : Type where
  | nil
  | cons (x : String) (xs : ListS)

def lengthS (xs : ListS) :=
  match xs with
  | .nil => 0
  | .cons  xs => lengthS xs + 1
```
)
#align(center,
```lean
lengthN xs + lengthS ys
```)

= Evaluation
Three RQs:
+ Is rank-1 enough to be useful
+ Does Chako produce false positives (Soundness)
+ How often does Chako produce false negatives (Completeness)

Data set:
- #sound_num_total theorems mined from $9$ standard library theories
- #perf_num_total potentially false statements generated through mutation

= Soundness Experiment
#[
#show strong: it => text(weight: "bold", it.body)
#set text(font: "New Computer Modern")
#align(center,
  sound_table
)]

= Completeness Experiment

#[
#show strong: it => text(weight: "bold", it.body)
#align(center,
  perf_table
)]

= Summary
- Developed an encoding from a fragment of Lean to Nunchaku
- Extensible for future work
- Implemented as a tactic integrated with Lean
- Sound in practice
- Good success rate in synthetic benchmarks
