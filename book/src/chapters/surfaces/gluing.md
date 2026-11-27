# Points and gluing

The seams of a mesh say which points of which edges belong together. This chapter turns that into a space: the surface is the set of points of all the triangles, with glued points identified.

## Points of a mesh

@decl SourceAbstract.Mesh.Point

A point of the mesh `M` is a pair `⟨f, x⟩` of a face `f` and a point `x` of the closed triangle of that face. The book calls it a *tagged point*: it remembers which triangle it lies in. In Lean the first component is written `p.1` and the position in the plane `p.2.val`.

A point in the interior of a triangle has one tag. A point on a seam has two, one in each of the faces along the seam. A corner has one tag for each face around it. Tagged points with different tags are different, even when a seam says that they should be the same point. The next definition records what the seams say.

## The gluing relation

@decl SourceAbstract.Mesh.glue

`M.glue p q` holds when some seam `s` and some point `x` of its first edge are such that `p` is `x` tagged with the first face, and `q` is `identify s x` tagged with the last face. In words: `p` and `q` are the two ends of one piece of tape.

::: check
- The relation is *directed*, from the first edge of a seam to its last. It is not symmetric, not reflexive and not transitive. It is a list of generators, not yet an equivalence relation.
- Around a corner of the surface, the tags of that corner are related by a chain of seams, one seam at a time. No single `glue` step relates the first to the last.
:::

## The surface

@decl SourceAbstract.Mesh.Surface SourceAbstract.Mesh.point

`M.Surface` is the quotient of the tagged points by the gluing relation, and `M.point p` is the point of the surface represented by the tagged point `p`.

Lean's `Quot` accepts any relation, and identifies two elements exactly when they are related by the smallest equivalence relation containing it. So two tagged points give the same point of the surface when they are joined by a finite chain of gluing steps, each used in either direction. Mathlib states this as `Quot.eq`: `Quot.mk r a = Quot.mk r b ↔ Relation.EqvGen r a b`. The docstring of [[SourceAbstract.Mesh.Point]] says the same in words.

::: check
- **Every point of the surface comes from a tagged point.** `M.point` is surjective, as for every quotient.
- **The topology of the surface.** Mathlib equips the tagged points with the topology of a disjoint union of triangles, and the quotient with the quotient topology: a set of the surface is open when its preimage in every triangle is open. Later definitions use words that depend on a topology: `Path` and `Continuous` in [Chapter 4](cut-locus.html) and [Chapter 7](source-unfoldings.html), `closure` in the definition of the cut locus. All of them refer to this quotient topology, which Lean finds by instance resolution.
- **The distance does not define the topology.** [Chapter 3](distance.html) defines a distance on the surface as a plain function. It is not registered as a metric structure, so Lean never uses it for continuity. For a finite mesh the quotient topology and the topology of the distance agree, by a standard compactness argument, but the abstract file does not state this.
:::
