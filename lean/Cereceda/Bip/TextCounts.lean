/-
Cereceda/Bip/TextCounts.lean — two steps of the text of Section 3: the count of colours that shows where the greedy
choice of `μ` can fail (short v4.24 l. 503-505), and the example on two vertices after Lemma 3.4 (l. 474-477).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Instance
import Cereceda.Defs.Example2
import Cereceda.Setting.Small

namespace Cereceda

open Finset

namespace TextCounts

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The colours of the list below the larger of `α v` and `β v` are colours of out-neighbours (in `α` or in `β`),
so there are at most `|N⁺(v)|` of them. -/
theorem card_low_le (I : Instance W) (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (v : W)
    (hv : v ≠ I.sink) : ((I.L v).filter (fun y => ¬ max (α v) (β v) ≤ y)).card ≤ (I.out v).card := by
  rcases le_total (α v) (β v) with hab | hab
  · have hsub : (I.L v).filter (fun y => ¬ max (α v) (β v) ≤ y) ⊆ (I.out v).image β := by
      intro y hy
      rw [mem_filter, not_le, max_eq_right hab] at hy
      exact (hβ.2 v hv).2.2 y hy.1 hy.2
    exact (card_le_card hsub).trans card_image_le
  · have hsub : (I.L v).filter (fun y => ¬ max (α v) (β v) ≤ y) ⊆ (I.out v).image α := by
      intro y hy
      rw [mem_filter, not_le, max_eq_left hab] at hy
      exact (hα.2 v hv).2.2 y hy.1 hy.2
    exact (card_le_card hsub).trans card_image_le

/-- In `{0,1,2,3}`, at most two colours below `M` and at most two from `M` up force `M = 2`. -/
theorem eq_two_of_cards : ∀ M : Fin 4, (univ.filter (fun y : Fin 4 => ¬ M ≤ y)).card ≤ 2 →
    (univ.filter (fun y : Fin 4 => M ≤ y)).card ≤ 2 → M = 2 := by
  decide

end TextCounts

open TextCounts

/-- Section 3, v4.24 l. 503-505: "We shall choose `μ` greedily, in instance order (Definition 3.7). A count of colours
shows that this can fail only at a vertex on `2` in `α` or in `β` whose two out-neighbours take both `2` and `3` in
`μ`." If no colour of `L(v)` is at least `max(α(v), β(v))` and free of the colours `μ(u)` of the out-neighbours `u` of
`v`, then `v` is on `2` in `α` or in `β`, and two out-neighbours of `v` take `2` and `3` in `μ`. The count uses only
the lists and the greedy colourings `α`, `β`: no bipartiteness, no single-sink hypothesis, nothing about `μ` before
`v` (the hypotheses `g = 0`, single-sink, `μ(s) = x` and the greedy rule for `μ` before `v` are not needed). -/
theorem sec3_mu_count_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W)
    (α β μ : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (v : W) (hv : v ≠ I.sink)
    (hfail : ¬ ∃ y ∈ I.L v, max (α v) (β v) ≤ y ∧ ∀ u ∈ I.out v, μ u ≠ y) :
    (α v = 2 ∨ β v = 2) ∧ ∃ u ∈ I.out v, ∃ w ∈ I.out v, μ u = 2 ∧ μ w = 3 := by
  -- every colour of `L(v)` from `max(α v, β v)` up is the colour in `μ` of an out-neighbour
  have hhigh : (I.L v).filter (fun y => max (α v) (β v) ≤ y) ⊆ (I.out v).image μ := by
    intro y hy
    rw [mem_filter] at hy
    by_contra hy'
    exact hfail ⟨y, hy.1, hy.2, fun u hu hμ => hy' (mem_image.2 ⟨u, hu, hμ⟩)⟩
  have hhc := (card_le_card hhigh).trans card_image_le
  have hlc := card_low_le I α β hα hβ v hv
  have hsplit := card_filter_add_card_filter_not (s := I.L v) (fun y => max (α v) (β v) ≤ y)
  have hk := I.out_card v
  have hL := I.L_card v
  have hL4 : (I.L v).card = 4 := by
    have := card_le_univ (I.L v)
    simp only [Fintype.card_fin] at this
    omega
  have hLu : I.L v = univ := eq_univ_of_card _ (by simpa using hL4)
  rw [hLu] at hhigh hhc hlc
  have hM : max (α v) (β v) = 2 := eq_two_of_cards _ (hlc.trans hk) (hhc.trans hk)
  rw [hM] at hhigh
  obtain ⟨u, hu, hμu⟩ := mem_image.1 (hhigh (mem_filter.2 ⟨mem_univ 2, le_rfl⟩))
  obtain ⟨w, hw, hμw⟩ := mem_image.1 (hhigh (mem_filter.2 ⟨mem_univ 3, by decide⟩))
  refine ⟨?_, u, hu, w, hw, hμu, hμw⟩
  rcases max_choice (α v) (β v) with h | h
  · exact Or.inl (h ▸ hM)
  · exact Or.inr (h ▸ hM)

namespace Ex2Aux

/-- `α` of the example: `(s, u) ↦ (1, 0)`. -/
def alpha2 : Fin 2 → Fin 4 := ![1, 0]

/-- `β` of the example: `(s, u) ↦ (0, 1)`. -/
def beta2 : Fin 2 → Fin 4 := ![0, 1]

theorem adj_iff (u v : Fin 2) : ex2.graph.Adj u v ↔ (u ≠ v ∧ (v ∈ ex2Out u ∨ u ∈ ex2Out v)) := by
  simp only [Skeleton.graph, SimpleGraph.fromRel_adj]
  exact Iff.rfl

theorem alpha_greedy : ex2.IsGreedy ex2.x alpha2 := by
  unfold Instance.IsGreedy IsLeastFree
  decide

theorem beta_greedy : ex2.IsGreedy ex2.g beta2 := by
  unfold Instance.IsGreedy IsLeastFree
  decide

theorem alpha_eq {α : Fin 2 → Fin 4} (hα : ex2.IsGreedy ex2.x α) : α = alpha2 :=
  (def_2_2_greedy_proved ex2 ex2.x).unique hα alpha_greedy

theorem beta_eq {β : Fin 2 → Fin 4} (hβ : ex2.IsGreedy ex2.g β) : β = beta2 :=
  (def_2_2_greedy_proved ex2 ex2.g).unique hβ beta_greedy

end Ex2Aux

open Ex2Aux

/-- Section 3, v4.24 l. 474-477 (the example after Lemma 3.4, instance `ex2`: sink `s` = `0` with the list `{0,1}` and
`x = 1`, one more vertex `u` = `1` with `N⁺(u) = {s}` and the list `{0,1,2,3}`): `α` and `β` exist; "Then `α(u) = 0` and
`β(u) = 1`. We can take `μ(u) = 2`": `μ = (s ↦ 1, u ↦ 2)` satisfies the hypotheses of Lemma 3.4 (proper, in the lists,
at least `α` and `β`, `μ(s) = x`); "Neither `s` nor `u` can move directly to its colour in `β`, the current colour of
the other. So `u` first rises to `2`, then `s` moves to `0`, and `u` moves down to `1`": the moves `(u, 2), (s, 0),
(u, 1)` are a sequence from `α` to `β`. -/
theorem sec3_example_two_proved :
    (∃ α, ex2.IsGreedy ex2.x α) ∧ (∃ β, ex2.IsGreedy ex2.g β) ∧
    ∀ α β : Fin 2 → Fin 4, ex2.IsGreedy ex2.x α → ex2.IsGreedy ex2.g β →
      α 1 = 0 ∧ β 1 = 1 ∧
      (IsProperFn ex2.graph (![1, 2] : Fin 2 → Fin 4) ∧ (∀ v, (![1, 2] : Fin 2 → Fin 4) v ∈ ex2.L v) ∧
        (∀ v, α v ≤ (![1, 2] : Fin 2 → Fin 4) v ∧ β v ≤ (![1, 2] : Fin 2 → Fin 4) v) ∧
        (![1, 2] : Fin 2 → Fin 4) ex2.sink = ex2.x) ∧
      ¬ LegalMove ex2.graph ex2.L α (0, β 0) ∧ ¬ LegalMove ex2.graph ex2.L α (1, β 1) ∧
      ex2.IsSeq α [(1, 2), (0, 0), (1, 1)] β := by
  refine ⟨⟨_, alpha_greedy⟩, ⟨_, beta_greedy⟩, fun α β hα hβ => ?_⟩
  obtain rfl := alpha_eq hα
  obtain rfl := beta_eq hβ
  refine ⟨rfl, rfl, ⟨?_, by decide, by decide, rfl⟩, ?_, ?_, ?_⟩
  · unfold IsProperFn
    simp only [adj_iff]
    decide
  · simp only [LegalMove, adj_iff]
    decide
  · simp only [LegalMove, adj_iff]
    decide
  · unfold Instance.IsSeq
    simp only [IsSeq, LegalMove, adj_iff]
    decide

end Cereceda
