#import "@preview/ctheorems:1.1.3": *
#import "@preview/codelst:2.0.2": sourcecode
#import "@preview/diagraph:0.3.0": raw-render
#import "@preview/curryst:0.3.0"
#import "@preview/lovelace:0.3.0"
#import "@preview/cetz:0.3.3" : canvas, draw, coordinate

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let corollary = thmplain(
  "corollary",
  "Corollary",
  base: "theorem",
  titlefmt: strong
)
#let definition = thmbox(
  "definition",
  "Definition",
  inset: (x: 1.2em, top: 1em),
  breakable: true
)

#let example = thmplain("example", "Example").with(numbering: none)
#let trivia = thmplain("trivia", "Trivia").with(numbering: none)
#let proof = thmproof("proof", "Proof")

#let dotrender = raw-render

#let inf-rule = curryst.rule

#let proof-tree = curryst.proof-tree

#let pseudocode(..e) = lovelace.pseudocode-list(booktabs: true, booktabs-stroke: 1pt + black, ..e)

#let core-settings(
  title: "Some Notes",
  author: "Henrik Böving",
  paper-size: "a4",
  lang: "en",
  body
) = {
  set document(title: title, author: author)
  set text(font: "New Computer Modern", size: 11pt, lang: "en")
  set page(paper: paper-size)
  set heading(numbering: "1.1")
  set par(justify: true)
  set list(indent: 1em)
  set enum(indent: 1em)
  set text(lang: lang)

  // Builtin show rules
  show link: set text(fill: blue.darken(60%))
  show raw: set text(font: "JuliaMono", size: 9pt)

  // Library show rules
  show: thmrules

  body
}

#let notes(
  title: "Some Notes",
  author: "Henrik Böving",
  paper-size: "a4",
  lang: "en",
  show-outline: true,
  body
) = {
  show: core-settings.with(
    title: title,
    author: author,
    paper-size: paper-size,
    lang: lang
  )

  set page(numbering : "1")
  // Title page
  align(center)[
    #text(2em, weight: 700, title)

    #text(1.00em, author)
  ]

  v(10pt)

  if show-outline {
    outline()
  }

  body
}

#let official(
  title: "",
  author: "Henrik Böving",
  email: "H.Boeving@campus.lmu.de",
  paper-size: "a4",
  lang: "en",
  matriculation: "",
  thesis-type: "",
  supervisor: "",
  submission_date: "",
  show-outline: true,
  body
) = {
  show: core-settings.with(
    title: title,
    author: author,
    paper-size: paper-size,
    lang: lang
  )


  set align(center)
  // Institution
  v(5%)
  text(14pt, smallcaps("Ludwig-Maximilians-Universität München"))
  linebreak()
  text(14pt, smallcaps("Chair of theoretical Computer Science and Theorem Proving"))
  v(5%)
  image("lmu-sigillium.svg", width: 20%)

  // Title
  v(5%)
  line(length: 105%)
  text(16pt, weight: 500, title)
  line(length: 105%)
  v(5%)
  text(14pt)[#thesis-type]
  linebreak()
  text(14pt)[in course type Computer Science]

  // Author information
  v(1fr) // push to bottom
  set align(left)
  grid(
    columns: (100pt, 1fr),
    gutter: 1em,
    "Student:", [#author],
    "E-Mail:", [#email],
    "Matr. number:", [#matriculation],
    "Supervisor:", [#supervisor],
    "Submission date:", [#submission_date],
  )
  v(5%)

  pagebreak()

  if show-outline {
    outline()
  }

  body
}
