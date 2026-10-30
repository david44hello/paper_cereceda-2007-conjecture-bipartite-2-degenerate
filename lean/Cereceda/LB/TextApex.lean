/-
Cereceda/LB/TextApex.lean — the text's steps on the apices: `J_ℓ` from `H_ℓ`, the fan's apex against `a` and `b`, leaving
the colour `3`, moves around apex moves, no apex move (short v4.24 l. 190-191, 194, 693-696, 701-704, 712-713, 718-719, 754-757).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

PROOF ROUTE: the splitting and the two apex facts unfold the adjacency of `pathApex`. The fan: a movable apex and its
new colour are two colours that no path vertex has. `H_ℓ`: the path colours `0, 2, 1, 2, 0, 2, 1, …` leave the colour
`2` to `a` and `0` to `b`. The moves before and after an apex move, and the case without apex moves, are
`walk_apex_halves` and `walk_no_apex_move` (LB/LowerBounds.lean) with the `q` of Propositions 4.1 and 4.6.
-/
import Cereceda.LB.LowerBounds

namespace Cereceda.TextApexAux

open Cereceda Finset LBAux

/-! ### Adjacency of `H_n` and `J_n` between a path vertex and an apex -/

lemma Hadj_inl_inr (n : ℕ) (i : Fin n) (b : Fin 2) : (Hgraph n).Adj (.inl i) (.inr b) ↔ i.val % 2 = b.val :=
  Fin.ext_iff

lemma Hadj_inr_inl (n : ℕ) (b : Fin 2) (i : Fin n) : (Hgraph n).Adj (.inr b) (.inl i) ↔ i.val % 2 = b.val :=
  Fin.ext_iff

lemma Jadj_inl_inr (n : ℕ) (i : Fin n) (k : Fin 4) : (Jgraph n).Adj (.inl i) (.inr k) ↔ (i.val + 1) % 4 = k.val :=
  Fin.ext_iff

lemma Jadj_inr_inl (n : ℕ) (k : Fin 4) (i : Fin n) : (Jgraph n).Adj (.inr k) (.inl i) ↔ (i.val + 1) % 4 = k.val :=
  Fin.ext_iff

/-! ### A plain colouring of `H_n` whose path uses three colours and in which `a` and `b` can move -/

/-- Path vertex `i` (0-based): `2` if `i` is odd; `0` if `i ≡ 0 (mod 4)`; `1` if `i ≡ 2 (mod 4)`. Apices: `3`. -/
def threeCol (n : ℕ) : Fin n ⊕ Fin 2 → Fin 4
  | .inl i => if i.val % 2 = 1 then 2 else if i.val % 4 = 0 then 0 else 1
  | .inr _ => 3

lemma threeCol_proper (n : ℕ) : IsProperFn (Hgraph n) (threeCol n) := by
  rintro (i | a) (j | b) h
  · change i.val + 1 = j.val ∨ j.val + 1 = i.val at h
    simp only [threeCol]
    split_ifs <;> first | decide | (exfalso; omega)
  · simp only [threeCol]
    split_ifs <;> decide
  · simp only [threeCol]
    split_ifs <;> decide
  · exact h.elim

lemma threeCol_card (n : ℕ) (hn : 3 ≤ n) : (univ.image (fun i : Fin n => threeCol n (.inl i))).card = 3 := by
  have hsub : univ.image (fun i : Fin n => threeCol n (.inl i)) ⊆ {0, 1, 2} := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := mem_image.1 hx
    simp only [threeCol]
    split_ifs <;> simp
  have hsup : ({0, 1, 2} : Finset (Fin 4)) ⊆ univ.image (fun i : Fin n => threeCol n (.inl i)) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_image]
    rcases hx with rfl | rfl | rfl
    · exact ⟨⟨0, by omega⟩, mem_univ _, by simp [threeCol]⟩
    · exact ⟨⟨2, by omega⟩, mem_univ _, by simp [threeCol]⟩
    · exact ⟨⟨1, by omega⟩, mem_univ _, by simp [threeCol]⟩
  have h3 : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
  have e1 := card_le_card hsub
  have e2 := card_le_card hsup
  omega

/-- In `threeCol`, `a = Sum.inr 0` can move to the colour `2`: its neighbours are the even path vertices. -/
lemma threeCol_move_a (n : ℕ) : LegalMove (Hgraph n) (fun _ => univ) (threeCol n) (.inr 0, 2) := by
  refine ⟨show (2 : Fin 4) ≠ 3 by decide, mem_univ _, ?_⟩
  rintro (i | b) hu
  · have hi := (Hadj_inr_inl n 0 i).1 hu
    simp only [Fin.val_zero] at hi
    show threeCol n (.inl i) ≠ 2
    simp only [threeCol]
    split_ifs <;> first | decide | (exfalso; omega)
  · exact hu.elim

/-- In `threeCol`, `b = Sum.inr 1` can move to the colour `0`: its neighbours are the odd path vertices. -/
lemma threeCol_move_b (n : ℕ) : LegalMove (Hgraph n) (fun _ => univ) (threeCol n) (.inr 1, 0) := by
  refine ⟨show (0 : Fin 4) ≠ 3 by decide, mem_univ _, ?_⟩
  rintro (i | b) hu
  · have hi := (Hadj_inr_inl n 1 i).1 hu
    simp only [Fin.val_one] at hi
    show threeCol n (.inl i) ≠ 0
    simp only [threeCol]
    split_ifs
    decide
  · exact hu.elim

/-! ### The flatness hypothesis of `walk_lower_bound` for `H_n` and `J_n` -/

lemma flatH (n : ℕ) : ∀ c : Fin n ⊕ Fin 2 → Fin 4, IsProperFn (Hgraph n) c → IsPlain c →
    (∃ j y, LegalMove (Hgraph n) (fun _ => univ) c (.inr j, y)) → ∀ g, IsPathHeight c g →
      ((g (n - 1) - g 0 : ℤ) : ℝ) ≤ ((n : ℝ) - 1) - ((n : ℝ) - 5) ∧
        -((n : ℝ) - 1) + ((n : ℝ) - 5) ≤ ((g (n - 1) - g 0 : ℤ) : ℝ) := by
  intro c hc hp hmove g hg
  have hW := abs_le.mp (lem_4_3_proved n c hc hp hmove g hg)
  have e1 : ((g (n - 1) - g 0 : ℤ) : ℝ) ≤ 4 := by exact_mod_cast hW.2
  have e2 : (-4 : ℝ) ≤ ((g (n - 1) - g 0 : ℤ) : ℝ) := by exact_mod_cast hW.1
  constructor <;> linarith

lemma flatJ (n : ℕ) : ∀ c : Fin n ⊕ Fin 4 → Fin 4, IsProperFn (Jgraph n) c → IsPlain c →
    (∃ j y, LegalMove (Jgraph n) (fun _ => univ) c (.inr j, y)) → ∀ g, IsPathHeight c g →
      ((g (n - 1) - g 0 : ℤ) : ℝ) ≤ ((n : ℝ) - 1) - ((n : ℝ) - 29) / 4 ∧
        -((n : ℝ) - 1) + ((n : ℝ) - 29) / 4 ≤ ((g (n - 1) - g 0 : ℤ) : ℝ) := by
  intro c hc hp hmove g hg
  have hW := abs_le.mp (lem_4_7_proved n c hc hp hmove g hg)
  push_cast
  constructor <;> linarith [hW.1, hW.2]

end Cereceda.TextApexAux

namespace Cereceda

open Finset LBAux TextApexAux

/-- Section 4.2, v4.24 l. 718-719: "We obtain `J_ℓ` from `H_ℓ` by splitting `a` into `a_1` and `a_3`, and `b` into `a_0`
and `a_2`, each new vertex keeping every second path neighbour of the old one." Merging `a_1, a_3` into `a = Sum.inr 0`
and `a_0, a_2` into `b = Sum.inr 1` (`a_j ↦ (j + 1) mod 2`) sends the edges of `J_ℓ` exactly onto the edges of `H_ℓ`; and
the apices of `J_ℓ` at two path vertices two apart (`v_{i+1}`, `v_{i+3}`, consecutive path neighbours of one old apex)
come from the same old apex but are different: each new vertex keeps every second path neighbour. -/
theorem sec4_J_from_H_proved (n : ℕ) :
    (∀ u v : Fin n ⊕ Fin 2, (Hgraph n).Adj u v ↔ ∃ u' v' : Fin n ⊕ Fin 4, (Jgraph n).Adj u' v' ∧
      Sum.map id (fun k : Fin 4 => (⟨(k.val + 1) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) u' = u ∧
      Sum.map id (fun k : Fin 4 => (⟨(k.val + 1) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) v' = v) ∧
    ∀ (i : ℕ) (hi : i + 2 < n) (k k' : Fin 4), (Jgraph n).Adj (.inl ⟨i, by omega⟩) (.inr k) →
      (Jgraph n).Adj (.inl ⟨i + 2, hi⟩) (.inr k') →
      (⟨(k.val + 1) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = ⟨(k'.val + 1) % 2, Nat.mod_lt _ (by norm_num)⟩ ∧
        k ≠ k' := by
  refine ⟨fun u v => ⟨fun h => ?_, ?_⟩, fun i hi k k' hk hk' => ?_⟩
  · rcases u with i | a <;> rcases v with j | b
    · exact ⟨.inl i, .inl j, h, rfl, rfl⟩
    · refine ⟨.inl i, .inr ⟨(i.val + 1) % 4, Nat.mod_lt _ (by norm_num)⟩, (Jadj_inl_inr n _ _).2 rfl, rfl, ?_⟩
      have hb := (Hadj_inl_inr n i b).1 h
      simp only [Sum.map_inr, Sum.inr.injEq, Fin.ext_iff]
      omega
    · refine ⟨.inr ⟨(j.val + 1) % 4, Nat.mod_lt _ (by norm_num)⟩, .inl j, (Jadj_inr_inl n _ _).2 rfl, ?_, rfl⟩
      have ha := (Hadj_inr_inl n a j).1 h
      simp only [Sum.map_inr, Sum.inr.injEq, Fin.ext_iff]
      omega
    · exact h.elim
  · rintro ⟨u', v', h, rfl, rfl⟩
    rcases u' with i | a <;> rcases v' with j | b
    · exact h
    · have hb := (Jadj_inl_inr n i b).1 h
      simp only [Sum.map_inl, Sum.map_inr, id_eq, Hadj_inl_inr]
      omega
    · have ha := (Jadj_inr_inl n a j).1 h
      simp only [Sum.map_inl, Sum.map_inr, id_eq, Hadj_inr_inl]
      omega
    · exact h.elim
  · have e := (Jadj_inl_inr n _ k).1 hk
    have e' := (Jadj_inl_inr n _ k').1 hk'
    simp only at e e'
    refine ⟨Fin.ext (by simp only; omega), fun hkk => ?_⟩
    rw [hkk] at e
    omega

/-- Remark 4.5, v4.24 l. 712-713: "The apex of the fan can move only when the path uses at most two colours, whereas `a`
and `b` can move when the path still uses three". (1) In a proper colouring of the fan (`pathApex n 1`, one apex
joined to every path vertex) that allows a move of the apex, the path uses at most two colours (it avoids the colour of
the apex and the new colour). (2) For `ℓ ≥ 3` there is a plain proper colouring of `H_ℓ` whose path uses exactly three
colours and in which `a` (`Sum.inr 0`) can move and `b` (`Sum.inr 1`) can move. -/
theorem rem_4_5_fan_apex_proved :
    (∀ n (c : Fin n ⊕ Fin 1 → Fin 4), IsProperFn (pathApex n 1 (fun _ => 0)) c →
      (∃ y, LegalMove (pathApex n 1 (fun _ => 0)) (fun _ => Finset.univ) c (.inr 0, y)) →
      (Finset.univ.image (fun i : Fin n => c (.inl i))).card ≤ 2) ∧
    ∀ n, 3 ≤ n → ∃ c : Fin n ⊕ Fin 2 → Fin 4, IsProperFn (Hgraph n) c ∧ IsPlain c ∧
      (Finset.univ.image (fun i : Fin n => c (.inl i))).card = 3 ∧
      (∃ y, LegalMove (Hgraph n) (fun _ => Finset.univ) c (.inr 0, y)) ∧
      (∃ y, LegalMove (Hgraph n) (fun _ => Finset.univ) c (.inr 1, y)) := by
  refine ⟨fun n c hc hm => ?_, fun n hn => ?_⟩
  · obtain ⟨y, hy, -, hadj⟩ := hm
    have hsub : univ.image (fun i : Fin n => c (.inl i)) ⊆ (univ.erase (c (.inr 0))).erase y := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := mem_image.1 hx
      have h1 : c (.inl i) ≠ c (.inr 0) := hc _ _ rfl
      have h2 : c (.inl i) ≠ y := hadj (.inl i) rfl
      exact mem_erase.2 ⟨h2, mem_erase.2 ⟨h1, mem_univ _⟩⟩
    have hcard : ((univ.erase (c (.inr 0))).erase y).card = 2 := by
      rw [card_erase_of_mem (mem_erase.2 ⟨hy, mem_univ _⟩), card_erase_of_mem (mem_univ _), card_univ,
        Fintype.card_fin]
    exact (card_le_card hsub).trans hcard.le
  · exact ⟨threeCol n, threeCol_proper n, fun _ => rfl, threeCol_card n hn, ⟨2, threeCol_move_a n⟩,
      ⟨0, threeCol_move_b n⟩⟩

/-- Section 1, v4.24 l. 190-191: "An additional vertex can leave the colour `3` only if its path neighbours miss one of
the other three colours": if the apex `Sum.inr j` has the colour `3` and can move (to `y`), then some colour `z ≠ 3`
(namely `y`) is on none of its path neighbours (the path vertices `v_{i+1}` with `f i = j`). -/
theorem intro_apex_leave3_proved (n k : ℕ) (f : Fin n → Fin k) (c : Fin n ⊕ Fin k → Fin 4) (j : Fin k) (y : Fin 4)
    (h3 : c (.inr j) = 3) (hm : LegalMove (pathApex n k f) (fun _ => Finset.univ) c (.inr j, y)) :
    ∃ z : Fin 4, z ≠ 3 ∧ ∀ i, f i = j → c (.inl i) ≠ z :=
  ⟨y, fun e => hm.1 (e.trans h3.symm), fun i hi => hm.2.2 (.inl i) hi⟩

/-- Section 1 (v4.24 l. 194, "order `ℓ²` moves precede the first move of an additional vertex, and as many follow the
last one") and the proofs of Propositions 4.1 and 4.6 (l. 701 and 704, "at least `(ℓ-5)²/16` moves precede `τ_1`" and
"follow `τ_2`"; l. 756-757, "at least `q²/16` moves before the first move of a vertex `a_j` and ... at least `q²/16`
after the last"): along every walk from `σ⁺` to `σ⁻` in `R_4(H_ℓ)` (`ℓ ≥ 5`, `q = ℓ - 5`), resp. `R_4(J_ℓ)` (`ℓ ≥ 29`,
`q = (ℓ - 29)/4`, so `q²/16 = (ℓ - 29)²/256`), every step `i` at which an apex changes its colour has at least `q²/16`
steps before it and at least `q²/16` steps after it. -/
theorem intro_lb_halves_proved :
    (∀ n : ℕ, 5 ≤ n → ∀ σp σm : (Hgraph n).Coloring (Fin 4), ⇑σp = sigmaPlus n 2 → ⇑σm = sigmaMinus n 2 →
      ∀ p : (recolGraph (Hgraph n) 4).Walk σp σm, ∀ i < p.length,
        (∃ j, (p.getVert i) (.inr j) ≠ (p.getVert (i + 1)) (.inr j)) →
        ((n : ℝ) - 5) ^ 2 / 16 ≤ (i : ℝ) ∧ ((n : ℝ) - 5) ^ 2 / 16 ≤ ((p.length - (i + 1) : ℕ) : ℝ)) ∧
    (∀ n : ℕ, 29 ≤ n → ∀ σp σm : (Jgraph n).Coloring (Fin 4), ⇑σp = sigmaPlus n 4 → ⇑σm = sigmaMinus n 4 →
      ∀ p : (recolGraph (Jgraph n) 4).Walk σp σm, ∀ i < p.length,
        (∃ j, (p.getVert i) (.inr j) ≠ (p.getVert (i + 1)) (.inr j)) →
        ((n : ℝ) - 29) ^ 2 / 256 ≤ (i : ℝ) ∧ ((n : ℝ) - 29) ^ 2 / 256 ≤ ((p.length - (i + 1) : ℕ) : ℝ)) := by
  refine ⟨fun n hn σp σm hσp hσm => ?_, fun n hn σp σm hσp hσm => ?_⟩
  · obtain rfl : σp = sigmaPlusCol n 2 _ := DFunLike.coe_injective hσp
    obtain rfl : σm = sigmaMinusCol n 2 _ := DFunLike.coe_injective hσm
    have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
    exact walk_apex_halves ((n : ℝ) - 5) (by linarith) (by linarith) (flatH n)
  · obtain rfl : σp = sigmaPlusCol n 4 _ := DFunLike.coe_injective hσp
    obtain rfl : σm = sigmaMinusCol n 4 _ := DFunLike.coe_injective hσm
    have hn' : (29 : ℝ) ≤ n := by exact_mod_cast hn
    have hq : ((n : ℝ) - 29) ^ 2 / 256 = (((n : ℝ) - 29) / 4) ^ 2 / 16 := by ring
    rw [hq]
    exact walk_apex_halves (((n : ℝ) - 29) / 4) (by linarith) (by linarith) (flatJ n)

/-- Proof of Proposition 4.1, v4.24 l. 693-696: "If `a` and `b` never move ... Hence at least `(ℓ−2)²/4 > (ℓ−5)²/8` moves
are needed". For `ℓ ≥ 5` and every walk from `σ⁺` to `σ⁻` in `R_4(H_ℓ)` along which no apex changes its colour: the
walk has at least `(ℓ² - 1)/4 ≥ (ℓ - 2)²/4` steps (Lean counts the full reversal directly, which gives the larger
`(ℓ² - 1)/4`), and `(ℓ - 2)²/4 > (ℓ - 5)²/8`. -/
theorem prop_4_1_no_move_proved (n : ℕ) (hn : 5 ≤ n) (σp σm : (Hgraph n).Coloring (Fin 4))
    (hσp : ⇑σp = sigmaPlus n 2) (hσm : ⇑σm = sigmaMinus n 2) (p : (recolGraph (Hgraph n) 4).Walk σp σm)
    (hno : ∀ i < p.length, ∀ j, (p.getVert i) (.inr j) = (p.getVert (i + 1)) (.inr j)) :
    ((n : ℝ) - 2) ^ 2 / 4 ≤ ((n : ℝ) ^ 2 - 1) / 4 ∧ ((n : ℝ) ^ 2 - 1) / 4 ≤ p.length ∧
      ((n : ℝ) - 5) ^ 2 / 8 < ((n : ℝ) - 2) ^ 2 / 4 := by
  obtain rfl : σp = sigmaPlusCol n 2 _ := DFunLike.coe_injective hσp
  obtain rfl : σm = sigmaMinusCol n 2 _ := DFunLike.coe_injective hσm
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨by nlinarith, walk_no_apex_move p hno, by nlinarith⟩

/-- Proof of Proposition 4.6, v4.24 l. 754-755: "If no `a_j` moves, at least `(ℓ−2)²/4 > (ℓ−29)²/128` moves are needed".
For `ℓ ≥ 29` and every walk from `σ⁺` to `σ⁻` in `R_4(J_ℓ)` along which no apex changes its colour: the walk has at
least `(ℓ² - 1)/4 ≥ (ℓ - 2)²/4` steps, and `(ℓ - 2)²/4 > (ℓ - 29)²/128`. -/
theorem prop_4_6_no_move_proved (n : ℕ) (hn : 29 ≤ n) (σp σm : (Jgraph n).Coloring (Fin 4))
    (hσp : ⇑σp = sigmaPlus n 4) (hσm : ⇑σm = sigmaMinus n 4) (p : (recolGraph (Jgraph n) 4).Walk σp σm)
    (hno : ∀ i < p.length, ∀ j, (p.getVert i) (.inr j) = (p.getVert (i + 1)) (.inr j)) :
    ((n : ℝ) - 2) ^ 2 / 4 ≤ ((n : ℝ) ^ 2 - 1) / 4 ∧ ((n : ℝ) ^ 2 - 1) / 4 ≤ p.length ∧
      ((n : ℝ) - 29) ^ 2 / 128 < ((n : ℝ) - 2) ^ 2 / 4 := by
  obtain rfl : σp = sigmaPlusCol n 4 _ := DFunLike.coe_injective hσp
  obtain rfl : σm = sigmaMinusCol n 4 _ := DFunLike.coe_injective hσm
  have hn' : (29 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨by nlinarith, walk_no_apex_move p hno, by nlinarith⟩

end Cereceda
