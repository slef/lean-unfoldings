# Vendored Jordan–Schönflies library

Source: https://github.com/alonamaloh/schoenflies-lean
Revision: `05a43d29cde026618777db3d4e4316204ccca237`
Author: Álvaro Begué. License: Apache 2.0 (see LICENSE).

Only library sources are included; upstream build caches and Comparator challenge
files are excluded. The upstream Lean/Mathlib version is 4.32.2.

For Lean/Mathlib 4.35 compatibility, source headers use the module system with
public imports and an exposed public section. Proof scripts in `InitialPair.lean` and
`Endgame.lean` use `Set.domRestrict` in place of its deprecated `Set.restrict`
alias. Proofs in `Graph/TwoConnected.lean`, `Graph/Tree.lean`, `Graph/Relabel.lean`,
and `InitialPair.lean` use the public vertex-set and incidence lemmas for graph
vertex deletion, replacing reductions of Mathlib implementation details.
No theorem statements changed. The Lake library configuration restores
the earlier elaborator transparency behavior with
`backward.isDefEq.respectTransparency.types=false`; the kernel still checks
all proofs. The unfolding axiom audit also checks the imported vendor modules.
