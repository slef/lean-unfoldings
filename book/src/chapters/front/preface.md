# Unfoldings in Lean

This book is a reader's guide to the formal statements of the `Unfoldings` library, a Lean 4 and Mathlib development about cutting polyhedral surfaces open and laying them flat. The library is large: more than three thousand files of proofs. Its claims are small. Two theorems are stated in *abstract* files, written to be read on their own:

- **Source unfolding.** Every point of a convex polyhedron that is not a vertex has a source unfolding: a planar, star-shaped net in which every straight segment from the centre folds to a shortest path ([Chapter 8](source-theorem.html)).
- **Nearly flat caps.** A convex cap whose faces are acute triangles and nearly horizontal can be cut along edges and unfolded to a simple polygon ([Chapter 12](cap-theorem.html)).

Each abstract file is under two hundred lines. It defines everything its theorem mentions, starting from Mathlib, and uses nothing else from the library in its definitions and statements. This book shows every one of those definitions exactly as Lean compiled it, and explains it.

::: caveat Status of this text
The explanations were drafted by an AI assistant from the Lean sources and have not yet been reviewed by the library's authors. The Lean code shown is extracted from the compiled library and cannot drift from it. The prose around it can be wrong. Where the prose states a mathematical fact that the abstract files do not prove, it says so.
:::

## Why a book about definitions

Lean checks proofs. It does not check that a theorem says what its name suggests. A statement about "nets" is only as good as the definition of a net: if the definition forgot to require that the net covers the surface, the theorem would be true and useless. So the work left to a human reader is to read the definitions and the statement, and to agree that they mean what we mean. Nothing else needs to be read; in particular, no proof.

The book is organized for that task.

- Every definition appears as a block of Lean source. Hover over any identifier to see its type and documentation, and click it to go to the place where it is explained. Identifiers from Mathlib link to the Mathlib documentation.
- Each block is followed by a plain description, and by a box **Reading the Lean** that lists the points where the formal text could be misread, and what the definition deliberately leaves out.
- Each theorem has a box at the top of its chapter with the statement in English. Ticking the box highlights, throughout the book, exactly the definitions that the statement depends on. The page [Checking a result](checking.html) explains this and lists the reading path of each theorem.
- The figures are interactive. They are computed in the browser by JavaScript written for this book, as illustrations. They are not checked by Lean, and the text never relies on them.

[Appendix A](audit.html) describes what is machine-checked: the proofs, the axioms, and the fact that the abstract files are self-contained.

## Map of the book

[Part I](part-surfaces.html) builds the surface. A polyhedral surface is given as a finite set of triangles, each in its own plane, with rules that pair their edges ([Chapter 1](meshes.html)). Pairing edges identifies points, and the surface is the quotient ([Chapter 2](gluing.html)). The surface carries an intrinsic distance, the length of the shortest route that stays on it ([Chapter 3](distance.html)), and with it shortest paths and the cut locus of a point ([Chapter 4](cut-locus.html)). A convex polyhedron is a way of placing the triangles in space so that they form the boundary of a convex body ([Chapter 5](polyhedra.html)).

[Part II](part-source.html) states the source-unfolding theorem. It defines what it means for a planar region to be a net of a surface in space ([Chapter 6](nets.html)), then what makes a net a source unfolding ([Chapter 7](source-unfoldings.html)), and states the theorem ([Chapter 8](source-theorem.html)).

[Part III](part-caps.html) states the cap theorem. Its abstract file is independent of the first one and repeats the definition of a mesh, with one addition: only some of the seams are kept, the others are cut ([Chapter 9](cap-meshes.html)). It defines convex caps ([Chapter 10](caps.html)) and edge unfoldings whose outline is a simple polygon ([Chapter 11](edge-unfoldings.html)), and states the theorem ([Chapter 12](cap-theorem.html)).

The two abstract files do not share code. Each can be checked without the other, at the price of some repetition, which [Chapter 9](cap-meshes.html) points out.

## What the library proves beyond these two statements

The library contains more than its abstract files state: the tree structure of the cut locus, a criterion for when a set of cut edges opens a convex polyhedron into a disk, refinements of triangulations, and an extension of the cap theorem to roofs with a non-planar rim. These results are stated in the library's own internal vocabulary, which is larger and was written for proving, not for reading. They are outside this book until they have abstract files of their own. The repository's README lists them.
