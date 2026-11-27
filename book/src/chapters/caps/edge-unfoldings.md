# Simple edge unfoldings

This chapter defines the conclusion of the cap theorem: the mesh can be cut along edges and laid flat, without overlap, so that its outline is a simple polygon.

## Simple polygons

@decl CapAbstract.SimplePolygon

A set `boundary` of the plane is a simple polygon, in the sense of a closed curve, when two things hold.

1. It is a finite union of closed segments.
2. It is the image of a closed loop without self-intersection: there is a map `loop` from the reals to the plane, continuous on $[0, 1]$, with `loop 0 = loop 1`, injective on $[0, 1)$, whose image of $[0, 1]$ is exactly `boundary`.

::: check
- **This is the curve, not the region it encloses.** `SimplePolygon` is a property of the outline.
- **Only $[0, 1]$ matters.** `loop` is defined on all reals for convenience; the conditions constrain it only on the unit interval.
- **Injective on $[0,1)$** means that the curve never passes twice through a point, except that it ends where it began. Together with continuity this makes the curve a Jordan curve.
- **Collinear consecutive segments are allowed**, as the docstring says. The definition does not count sides.
:::

## Edge unfoldings

@decl CapAbstract.HasSimpleEdgeUnfolding

`HasSimpleEdgeUnfolding M` says that there are a set `retain` of seams to keep and a rigid motion `place f` of the plane for each face, such that three things hold.

1. **The cut surface is a disk.** `M.Surface retain`, the surface glued along the retained seams only ([Chapter 9](cap-meshes.html)), is homeomorphic to the closed unit disk.
2. **The layout is exactly the cut surface.** Two tagged points are placed at the same point of the plane *if and only if* they are identified in the cut surface.
3. **The outline is a simple polygon.** The frontier of the union of the placed triangles satisfies `SimplePolygon`.

Condition 2 carries the content, and each direction says something different.

- *If two points are identified by retained seams, they are placed at the same point.* The faces remain attached along the seams that were kept. The layout is an unfolding of the cut surface, not a pile of loose triangles.
- *If two points are placed at the same point, they are identified by retained seams.* No two faces overlap, and no two points touch in the plane unless they were attached on the cut surface.

::: check
- **`place` here maps the plane to the plane.** Its type is `Plane ≃ᵃⁱ[ℝ] Plane`, a rigid motion of the plane. In the definition of a cap, `place` maps the plane to space. The two are different maps with the same name in different structures.
- **Reflections are allowed.** A rigid motion in this sense may be a reflection. Condition 2 keeps this harmless: two neighbouring faces that are attached along a seam must lie on opposite sides of it, otherwise their interiors would overlap. The whole layout may be the mirror image of the one you would draw.
- **Touching is excluded as well as overlap.** The second direction of condition 2 forbids even a corner of the layout touching another part of it, unless the two points were already attached. This is stronger than the usual "the interiors do not overlap".
- **The cap is not mentioned.** `HasSimpleEdgeUnfolding` is a property of the mesh alone: of its triangles and seams. How the mesh sits in space is irrelevant once its faces are known, as it should be.
- **Cuts along edges only.** Faces are never cut, since each face is placed whole by one rigid motion, and seams are kept or cut whole.
- **Condition 1 is nearly implied by the others.** A layout whose outline is a simple closed curve fills a disk. Stating it explicitly spares the reader that argument.
:::
