/-
Cereceda/Intro/PathClique.lean — the path joined to a clique on `d - 1` vertices is `d`-degenerate, and for `d = 2` it
is the fan (short v4.24 l. 112-113).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

PROOF ROUTE: the order `v_1, …, v_n`, then the clique. A path vertex has its later neighbours among the next path
vertex and the `d - 1` clique vertices (at most `d`); a clique vertex has its later neighbours among the clique
vertices (at most `d - 1`). An order with at most `d` later neighbours gives `d`-degenerate (`degenerate_of_order`).
-/
import Cereceda.Defs.PathClique
import Cereceda.LB.Facts

namespace Cereceda.PathCliqueAux

open Cereceda Finset

/-- A path vertex `v_{i+1}` has its later neighbours among the next path vertex (if any) and the clique. -/
lemma laterNbrs_inl_subset (n k : ℕ) (i : Fin n) :
    laterNbrs (pathClique n k) finSumFinEquiv (.inl i) ⊆
      insert (.inl ⟨min (i.val + 1) (n - 1), by have := i.isLt; omega⟩) (univ.map Function.Embedding.inr) := by
  intro u hu
  rw [laterNbrs, mem_filter] at hu
  obtain ⟨-, hadj, hlt⟩ := hu
  rw [mem_insert]
  rcases u with i' | a
  · left
    change i.val + 1 = i'.val ∨ i'.val + 1 = i.val at hadj
    rw [Fin.lt_def, FactsAux.rho_inl, FactsAux.rho_inl] at hlt
    rw [Sum.inl.injEq, Fin.ext_iff]
    show i'.val = min (i.val + 1) (n - 1)
    have := i'.isLt
    omega
  · right
    simp

/-- A clique vertex has its later neighbours in the clique: the path vertices come first. -/
lemma laterNbrs_inr_subset (n k : ℕ) (a : Fin k) :
    laterNbrs (pathClique n k) finSumFinEquiv (.inr a) ⊆ univ.map Function.Embedding.inr := by
  intro u hu
  rw [laterNbrs, mem_filter] at hu
  obtain ⟨-, -, hlt⟩ := hu
  rcases u with i | b
  · rw [Fin.lt_def, FactsAux.rho_inl, FactsAux.rho_inr] at hlt
    have := i.isLt
    omega
  · simp

/-- In the order path first, then the clique, every vertex has at most `k + 1` later neighbours. -/
lemma pathClique_order (n k : ℕ) :
    IsDegOrder (pathClique n k) (k + 1) (finSumFinEquiv : Fin n ⊕ Fin k ≃ Fin (n + k)) := by
  rintro (i | a)
  · refine (card_le_card (laterNbrs_inl_subset n k i)).trans ((card_insert_le _ _).trans ?_)
    rw [card_map, card_univ, Fintype.card_fin]
  · refine (card_le_card (laterNbrs_inr_subset n k a)).trans ?_
    rw [card_map, card_univ, Fintype.card_fin]
    omega

end Cereceda.PathCliqueAux

namespace Cereceda

open PathCliqueAux

/-- Section 1, v4.24 l. 112-113: the path joined to every vertex of a clique on `d - 1` vertices "is `d`-degenerate"
(for every `d ≥ 1` and every number `n` of path vertices), and for `d = 2` (a clique on one vertex) it is the fan
`pathApex n 1 (fun _ => 0)` of `intro_fans`. -/
theorem intro_path_clique_proved : (∀ n d : ℕ, 1 ≤ d → IsDegenerate (pathClique n (d - 1)) d) ∧
    ∀ n : ℕ, pathClique n 1 = pathApex n 1 (fun _ => 0) := by
  refine ⟨fun n d hd => ?_, fun n => ?_⟩
  · have := FactsAux.degenerate_of_order _ (d - 1 + 1) _ (pathClique_order n (d - 1))
    rwa [Nat.sub_add_cancel hd] at this
  · ext u v
    rcases u with i | a <;> rcases v with j | b
    · exact Iff.rfl
    · exact iff_of_true trivial (Subsingleton.elim _ _)
    · exact iff_of_true trivial (Subsingleton.elim _ _)
    · exact iff_of_false (fun h => h (Subsingleton.elim _ _)) id

end Cereceda
