# What Lean checks

A formal library rests on a short chain of trust. This appendix spells out each link, what checks it, and what is left to the reader. The table at the end is generated from the compiled library each time the book is built.

## The chain of trust

**1. The proofs.** Every theorem in the library is checked by Lean's kernel when the library is built with `lake build`.

**2. The axioms.** The file `Audit.lean` is one of the default build targets. Its first command goes through every declaration of every module of the library, and of the vendored planar-topology sources it depends on, and fails the build if any of them depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`. These are Lean's three standard axioms, the usual foundation for classical mathematics. `sorryAx`, the axiom behind unfinished proofs, is not among them. The badges in this book repeat that computation (`collectAxioms`) for each declaration shown.

**3. The statement boundary.** The second command of `Audit.lean` checks the two abstract files, `Unfoldings/Cap/Abstract.lean` and `Unfoldings/Source/Abstract.lean`. For every declaration of such a file it collects the constants that occur in its type and, unless the declaration is a theorem, in its body. The build fails if any of these constants is defined in another module of the library. Proofs of theorems are not inspected, so they may use the whole library. The consequence for a reader: *the definitions and statements of an abstract file can be read with that file and Mathlib alone*. The line "Statement reads only … and Mathlib" under each theorem of this book refers to this check.

**4. The definitions and statements.** This is the part no tool can check: whether `IsNetOf`, `cutLocus` or `Cap` mean what a geometer means. The chapters of this book exist for this step. Each definition is shown and explained, and the points where it could be misread are collected in the boxes "Reading the Lean".

::: caveat What was run for this edition
The Lean data of this book was extracted after building the two abstract modules and everything they import, which checks every proof they depend on. The axiom badges were computed from that build. The complete default build, which includes `Audit.lean` and the parts of the library that the abstract files do not use, was not rerun when the book was generated. The repository's continuous integration runs it.
:::

## What this book's build checks

- Every Lean name mentioned in the text resolves to a constant that Lean exported. Renamed or deleted declarations fail the build.
- Declaration positions come from the compiler's `.ilean` files, and each is checked against the current source: the declared name must appear where the compiler recorded it. A stale build fails.
- Code blocks are cut from the compiled sources by those positions, so they cannot drift from the library.
- Only declarations of the abstract files can be quoted or linked. The build fails if a chapter quotes an internal declaration.
- Reading paths are computed by Lean from the elaborated terms: for each theorem, the constants in its statement, and recursively those in the types and bodies of the definitions reached.
- Coverage: the build lists every declaration of the abstract files that the book does not show.
- Every citation refers to an entry of the bibliography, and each entry's DOI or arXiv identifier was checked against Crossref, DataCite or arXiv.

## What is not checked

- **The prose.** The explanations are written by hand. Where they state a mathematical fact that the abstract files do not contain, they say so, but no tool verifies them.
- **The figures.** They run JavaScript written for this book. A test suite checks them against consequences of the definitions on examples: seams pair every edge of a closed mesh once and preserve lengths, the computed source unfolding has the area of the surface and is star-shaped, radial segments fold to paths of the same length, the cap of the figure is convex with acute faces. These tests guard the illustrations. They are not evidence for the theorems, which need none beyond Lean's check.

## Deliberate non-claims

Collected from the chapters, for reference.

- The source-unfolding theorem excludes sources at vertices of the polyhedron ([Chapter 8](source-theorem.html#why-vertices-are-excluded)), and asserts existence only: no algorithm, no bound on the number of pieces, no uniqueness.
- The cut locus enters the statement through its definition only. That it is a tree is proved in the library, outside the reading interface ([Chapter 7](source-unfoldings.html)).
- The abstract file does not state that the intrinsic distance equals the infimum of the lengths of routes ([Chapter 3](distance.html#why-this-is-the-length-of-the-shortest-route)).
- Neither abstract file contains an example of its main structure, a `Polyhedron` or a `Cap` ([Chapter 5](polyhedra.html), [Chapter 10](caps.html)).
- The cap theorem gives no value for the tilt bound and no algorithm, and does not treat the closed polyhedron obtained by adding the base ([Chapter 12](cap-theorem.html#comparison-with-the-paper)).
- The roof theorem and the other results of the library have no abstract file and are not covered.

## Theorems of the reading interface

@audit
