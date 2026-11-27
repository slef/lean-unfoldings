# Checking a result

You may not want to read the whole book. Perhaps you only want to know whether the library really proves that convex polyhedra have source unfoldings. This page is for that.

## What there is to check

Lean checks every proof, so you never need to read one. What Lean cannot check is that a theorem *says what you think it says*. A statement can be true and still miss the point: a definition of "net" might forget that the net must cover the surface, or a hypothesis might be impossible to satisfy, which would make the theorem empty. To trust a result you have to read its statement, every definition the statement mentions, every definition *those* mention, and so on down to standard Mathlib notions such as the Euclidean plane, convex hulls, continuity and isometries.

That set of definitions is small. The book computes it from the compiled library: it starts from the statement and follows the types and bodies of definitions, but never proofs. For the source-unfolding theorem it is the content of one file of 180 lines.

Two things keep the list honest:

- **The boundary is checked by Lean.** The library's audit, part of its default build, verifies that the definitions and statements of each abstract file mention no declaration from the rest of the library ([Appendix A](audit.html)). So the reading path cannot leave the file, and every definition on it is quoted in this book.
- **Skips are listed.** If a definition on the path could be safely ignored, the book would list it as a skip together with the reason, so that you can disagree. No result currently skips anything.

The axioms behind each proof are listed in [Appendix A](audit.html). All of them are Lean's three standard axioms.

## How to use it

Each theorem's chapter opens with a box stating the result in English and in Lean. Select one or both results below, or tick the box in a chapter. To narrow the selection to a single result, use its **only this one** button. The selection then follows you through the book:

- the sidebar shows, for each chapter, how many definitions you need from it;
- on each page, those definitions are outlined and tagged **needed**;
- a bar at the bottom of the page steps through them in reading order, and can dim everything else.

The reading list at the bottom of this page collects everything in one place. It also lists the Mathlib notions that the statement uses directly, with links to their documentation.

## A checklist for a definition

When you read a definition, these are the questions the **Reading the Lean** boxes try to answer.

1. **Is it the usual notion?** If it differs from the textbook definition, is the difference harmless, a restriction, or a generalization?
2. **Can it be satisfied?** A structure with contradictory fields makes every theorem about it true. Look for an example.
3. **Does it hide a conclusion?** A hypothesis that already contains what the theorem should prove makes the theorem trivial.
4. **What do the quantifiers range over?** A bound "chosen before the mesh" and a bound that may depend on the mesh are different theorems.
5. **Which structure does a word refer to?** "Continuous" and "closure" refer to a topology, and a quotient has more than one natural candidate.

## The main results

@claims
