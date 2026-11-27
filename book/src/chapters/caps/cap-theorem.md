# The nearly flat cap theorem

```headline nearly-flat-cap
title: Nearly flat convex caps with acute faces unfold along edges to a simple polygon
source: @orourke2018
key: yes
theorems: CapAbstract.nearly_flat_cap

For every $\alpha > 0$ there is an angle $\varphi$ with $0 < \varphi < \pi/2$ such that every convex cap satisfying the following two conditions has an edge unfolding without overlap whose outline is a simple polygon: every angle of every face is at most $\pi/2 - \alpha$, and every face normal makes an angle at most $\varphi$ with the vertical.
```

## The statement

@stmt CapAbstract.nearly_flat_cap

Given a positive real `α`, the theorem produces an angle `φ` in the open interval $(0, \pi/2)$. Then, for every mesh `M` and every cap `K` on it ([Chapter 10](caps.html)), if `M` has acute margin `α` ([Chapter 9](cap-meshes.html)) and every normal of `K` has third coordinate at least $\cos\varphi$, the mesh has a simple edge unfolding ([Chapter 11](edge-unfoldings.html)).

::: check
- **The order of the quantifiers.** `∃ φ ∈ Set.Ioo 0 (π/2), ∀ {Face Seam} … (M) (K), …`. The angle is chosen first, knowing only `α`. It then works for all meshes, of any size and shape. A statement with the quantifiers the other way round, where the angle could depend on the mesh, would say almost nothing: every single cap can be flattened a little.
- **`Real.cos φ ≤ K.normal f 2`** says that the angle between the normal and the vertical is at most `φ`, because the normal is a unit vector pointing up and the cosine is decreasing on $[0, \pi/2]$.
- **`Set.Ioo`** is the open interval; `φ` is strictly between $0$ and $\pi/2$.
- **The conclusion is about `M`**, not about `K`. The cap enters only through the hypotheses.
- **The proof is longer than for the source theorem** but has the same nature: it builds the internal objects of the library from the fields of `M` and `K`, applies the internal theorem `orourke_cap_theorem`, and translates the result back. Open it with "show proof" to see that it contains no mathematics of its own.
:::

## Comparison with the paper

The abstract of @orourke2018 states the result as follows: a nearly flat, acutely triangulated convex cap has an edge unfolding to a non-overlapping polygon in the plane, where nearly flat means that every outer face normal forms a sufficiently small angle with the vertical, smaller than a bound $\Phi$ that depends on the acuteness gap $\alpha$.

| | Paper | Lean statement |
|---|---|---|
| Dependence of the bound | $\Phi$ depends on $\alpha$ only | `φ` is chosen from `α` before the mesh |
| Value of the bound | $\Phi \approx 0.36\sqrt{\alpha}$ suffices | existence of some `φ > 0`; no value |
| Outline of the unfolding | a non-overlapping polygon | a simple polygon; non-overlap including touching |
| Algorithm | constructive, at worst $O(n^2)$ | none stated |
| Closing the cap by its base | the closed polyhedron also unfolds | not stated |

So the Lean theorem is the existence part of the paper's main result. The docstring is explicit about one of the gaps: "No algorithmic time bound is asserted."

## What the theorem does not say

- **No explicit angle.** The theorem gives no formula or numerical value for `φ`.
- **Nothing for obtuse or right triangles.** With $\alpha \le 0$ the theorem does not apply.
- **Nothing for caps with a non-planar rim.** The library proves an extension to such surfaces, which it calls roofs, in `Roof/SimpleEdgeUnfolding.lean`. That result has no abstract file and is outside this book.
- **Nothing about closed convex polyhedra.** Whether every convex polyhedron has an edge unfolding without overlap remains open.
