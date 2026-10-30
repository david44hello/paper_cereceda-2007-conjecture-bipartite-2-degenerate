/-
Cereceda/Intro/ChordalKmn.lean — Remark 4.9: a complete bipartite graph is chordal bipartite, and a graph that embeds
as an induced subgraph into a bipartite graph is bipartite (short v4.24 l. 803-805).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

PROOF ROUTE: along a walk in `K_{m,n}` the side changes at every step, so the vertices at positions `0` and `3` of a
cycle lie on different sides and are adjacent. In a cycle of length at least `6` they are not consecutive: the
vertices at positions `1, …, length` are distinct and only position `length` repeats position `0`, so the edge
between them is a chord. An embedding is a homomorphism, and a 2-colouring pulls back along a homomorphism.
-/
import Cereceda.Defs.Intro

namespace Cereceda.ChordalKmnAux

open SimpleGraph

/-- An edge of a complete bipartite graph joins the two sides. -/
lemma side_flip {V W : Type} {x y : V ⊕ W} (h : (completeBipartiteGraph V W).Adj x y) :
    y.isLeft = !x.isLeft := by
  rcases x with a | a <;> rcases y with b | b <;> simp_all

/-- Two vertices on different sides of a complete bipartite graph are adjacent. -/
lemma adj_of_side {V W : Type} {x y : V ⊕ W} (h : y.isLeft = !x.isLeft) :
    (completeBipartiteGraph V W).Adj x y := by
  rcases x with a | a <;> rcases y with b | b <;> simp_all

/-- Along a walk in a complete bipartite graph, the vertex at position `3` is on the other side than the start. -/
lemma getVert_three_side {V W : Type} {u v : V ⊕ W} (w : (completeBipartiteGraph V W).Walk u v)
    (h3 : 3 ≤ w.length) : (w.getVert 3).isLeft = !u.isLeft := by
  have e0 := side_flip (w.adj_getVert_succ (i := 0) (by omega))
  have e1 := side_flip (w.adj_getVert_succ (i := 1) (by omega))
  have e2 := side_flip (w.adj_getVert_succ (i := 2) (by omega))
  rw [Walk.getVert_zero] at e0
  rw [e2, e1, e0, Bool.not_not]

/-- In a cycle of length at least `6`, the vertices at positions `0` and `3` are not joined by an edge of the cycle. -/
lemma not_mem_edges_zero_three {V : Type} {G : SimpleGraph V} {v : V} {w : G.Walk v v} (hw : w.IsCycle)
    (h6 : 6 ≤ w.length) : s(v, w.getVert 3) ∉ w.edges := by
  rw [Walk.mk_mem_edges_iff_exists]
  rintro ⟨i, hi, he⟩
  rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hi0 : i = 0 := by
      have := (hw.getVert_endpoint_iff hi.le).1 h1
      omega
    subst hi0
    have := hw.getVert_injOn (show 1 ≤ 0 + 1 ∧ 0 + 1 ≤ w.length from ⟨le_rfl, by omega⟩)
      (show 1 ≤ 3 ∧ 3 ≤ w.length from ⟨by omega, by omega⟩) h2
    omega
  · have hil : i + 1 = w.length := by
      have := (hw.getVert_endpoint_iff (by omega)).1 h2
      omega
    have := hw.getVert_injOn (show 1 ≤ i ∧ i ≤ w.length from ⟨by omega, by omega⟩)
      (show 1 ≤ 3 ∧ 3 ≤ w.length from ⟨by omega, by omega⟩) h1
    omega

end Cereceda.ChordalKmnAux

namespace Cereceda

open SimpleGraph ChordalKmnAux

/-- Remark 4.9, v4.24 l. 805: the complete bipartite graph `K_{m,n}` "is chordal bipartite": it is bipartite, and in
every cycle of length at least `6` the vertices at positions `0` and `3` are adjacent (they lie on different sides)
but not consecutive on the cycle, so they form a chord. -/
theorem rem_4_9_Kmn_chordal_proved (m n : ℕ) : IsChordalBipartite (completeBipartiteGraph (Fin m) (Fin n)) := by
  refine ⟨IsBipartite.completeBipartiteGraph _ _, fun v w hw h6 => ?_⟩
  exact ⟨v, w.start_mem_support, w.getVert 3, w.getVert_mem_support 3,
    adj_of_side (getVert_three_side w (by omega)), not_mem_edges_zero_three hw h6⟩

/-- Remark 4.9, v4.24 l. 803-804: "every graph built along the way is an induced subgraph of the final graph. If the
final graph is bipartite, so are all of them": a graph `G` that embeds into a bipartite graph `K` (as an induced
subgraph, `G ↪g K`) is bipartite. -/
theorem rem_4_9_bipartite_down_proved {V W : Type} (G : SimpleGraph V) (K : SimpleGraph W) (φ : G ↪g K)
    (hK : K.IsBipartite) : G.IsBipartite :=
  Colorable.of_hom φ.toHom hK

end Cereceda
