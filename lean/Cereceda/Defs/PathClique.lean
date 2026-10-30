/-
Cereceda/Defs/PathClique.lean — the graph of Section 1 that shows the order `n²` is best possible: a path joined to
every vertex of a clique (short v4.24 l. 112-113).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE: read against short v4.24 l. 112-113. Lean's `n` is the number of path vertices, `k` the number of
clique vertices (the paper's `d - 1`). INDEXING: the path vertex `Sum.inl i` (`i : Fin n`, 0-based) is `v_{i+1}`.
-/
import Cereceda.Defs.Basic

namespace Cereceda

/-- The graph of v4.24 l. 112-113: "Take a path and join every vertex of a clique on `d−1` vertices to every vertex of
the path (for `d = 2`, a fan)". The path is `v_1 ⋯ v_n` (`Sum.inl i`), the clique has the `k` vertices `Sum.inr a`
(`k = d - 1`); every clique vertex is joined to every path vertex, and the clique vertices are pairwise adjacent. -/
def pathClique (n k : ℕ) : SimpleGraph (Fin n ⊕ Fin k) where
  Adj a b := match a, b with
    | .inl i, .inl j => i.val + 1 = j.val ∨ j.val + 1 = i.val
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr a, .inr b => a ≠ b
  symm := ⟨fun a b h => by
    rcases a with i | i <;> rcases b with j | j <;> simp_all <;> omega⟩
  loopless := ⟨fun a h => by rcases a with i | i <;> simp_all⟩

instance (n k : ℕ) : DecidableRel (pathClique n k).Adj := fun a b =>
  match a, b with
  | .inl i, .inl j => inferInstanceAs (Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val))
  | .inl _, .inr _ => inferInstanceAs (Decidable True)
  | .inr _, .inl _ => inferInstanceAs (Decidable True)
  | .inr a, .inr b => inferInstanceAs (Decidable (a ≠ b))

end Cereceda
