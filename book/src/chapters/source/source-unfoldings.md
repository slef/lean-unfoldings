# Source unfoldings

A source unfolding is a net with a centre. The source sits at the origin of the plane, and straight segments from the origin are the shortest paths from the source.

@viz source {"solid": "box"}

On the right is the source unfolding of the solid on the left, computed for the source marked by the black dot. The orange outline of the net folds onto the orange cut locus on the solid. Point at the net: the blue segment from the origin folds to the blue path on the solid, a shortest path from the source. The second menu switches to the star unfolding from the same source, the subject of [Chapter 9](star-unfolding.html).

## The definition

@decl SourceAbstract.IsSourceUnfolding

`IsSourceUnfolding K source region fold` is stated for a polyhedron `K` on a mesh `M`, a tagged point `source`, and a region with a folding map as in [Chapter 6](nets.html). It asks first that the region and the folding form a net of the surface of `K`. Then it asks for a map `project` from the region to the surface `M.Surface`, with twelve properties. They fall into five groups.

### The projection is the folding

| | Lean | Meaning |
|---|---|---|
| a | `Continuous project` | `project` is continuous for the quotient topology of the surface |
| b | `Function.Surjective project` | every point of the surface is reached |
| c | `project z = M.point p → fold z = K.place p.1 p.2.val` | if `project z` is represented by the tagged point `p`, then `fold z` is the position of `p` in space |

`fold` takes values in space; `project` takes values in the abstract surface, where distances and the cut locus are defined. Property c says that they are the same map, seen in the two descriptions. Since the placement of a polyhedron is injective on the surface, `fold` determines `project`. The existential quantifier over `project` therefore hides no choice.

### The source is at the origin and the net is star-shaped

| | Lean | Meaning |
|---|---|---|
| d | `0 ∈ interior region` | the origin is an interior point of the net |
| e | `∀ z t, t • z.val ∈ region` | with every point $z$, the net contains the whole segment from the origin to $z$ |
| f | `project ⟨0, h⟩ = M.point source` | the origin folds to the source |

### The interior is the surface minus the cut locus

| | Lean | Meaning |
|---|---|---|
| g | `∃ H : interior region ≃ₜ (cutLocus …)ᶜ, …` | `project` restricts to a homeomorphism from the interior of the net onto the complement of the cut locus |
| h | `∀ x, ∃ T, IsOpen T ∧ x ∈ T ∧ …` | every interior point has a neighbourhood on which `project` preserves distances exactly |
| i | `project '' {z \| z.val ∈ frontier region} = cutLocus …` | the frontier of the net folds onto the cut locus, and onto nothing else |

Property h compares the Euclidean distance `edist y z` of two points of the net with the intrinsic distance of [Chapter 3](distance.html) between their images. Globally the two differ: two points of the net on either side of a cut are far apart in the plane and close on the surface. Locally they agree.

### Radial segments are shortest paths

| | Lean | Meaning |
|---|---|---|
| j | `M.distance (M.point source) (project z) = ENNReal.ofReal ‖z.val‖` | the distance on the surface from the source to the image of $z$ is the Euclidean norm of $z$ |
| k | `M.distance (project (s • z)) (project (t • z)) = ENNReal.ofReal ‖z.val‖ * edist s t` | along the segment from the origin to $z$, distances on the surface are proportional to the parameter |

Property k is the condition [[SourceAbstract.Mesh.Shortest]] for the path $t \mapsto$ `project` $(t z)$: the radial segment to $z$ folds to a shortest path, at constant speed, from the source to the image of $z$. Property j is the case of the two endpoints, and holds also for $z$ on the frontier.

### Every shortest path is a radial segment

| | Lean | Meaning |
|---|---|---|
| l | `∀ x (p : Path (M.point source) x), M.Shortest p → ∃! z : region, ∀ t, ∃ hz, project ⟨t • z.val, hz⟩ = p t` | each shortest path from the source is the image of the radial segment to exactly one point $z$ of the net |

This is the converse of k, with uniqueness. A point $x$ of the cut locus that is reached by three shortest paths has three different points $z$ on the frontier of the net, one for each path. The docstring calls these "distinct paths tied at one endpoint".

::: check
- **The source is a tagged point.** `source : M.Point` picks a face and a position in it. If the source lies on a seam it has several tags; all of them give the same `M.point source`, and the definition uses only that.
- **Property f is written with a hypothesis** `h : 0 ∈ region` because `project` is defined on the region and needs a proof that the origin belongs to it. By d the hypothesis always holds, so f is not vacuous.
- **Properties k and l need `t • z` to be in the region.** In k this is an explicit hypothesis (`hs`, `ht`), always true by e. In l it is part of the conclusion.
- **The definition is redundant, deliberately.** For example j follows from k, and b follows from the net conditions with c. Redundant conditions make the definition easier to believe and cost nothing: the theorem proves them all.
- **Nothing is said about the shape of the cut locus.** That it is a tree, with the vertices as leaves, is not part of this definition. The library proves it separately (`Source/CutTree.lean`), outside the reading interface.
- **Uniqueness is not claimed.** Properties j to l suggest that a source unfolding is determined up to a rotation or reflection of the plane about the origin. The definition does not say so, and the theorem only asserts existence.
:::

## What the figure computes

The figure does not use the Lean development. For the chosen source it enumerates the straight lines that leave the source, develops the faces they cross into the plane, and keeps, for every point of the surface, the copies that are closest to the origin. The test suite of this book checks, for each solid in the menu and several sources, that the result has the area of the surface, that it is star-shaped, and that each radial segment folds to a path of the same length. These are consequences of the definition above, checked numerically on examples. They are not a proof of anything.
