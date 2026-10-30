/-
Cereceda/Setting/TextMoves.lean — six steps of the text on moves and cones: a move changes a height by `±2` at the moved vertex
only (short v4.24 l. 303-304); in Lemma 2.4 the root moves at most once, and then directly to its target colour
(l. 316-317); recolouring a cone keeps every vertex outside it greedy (l. 134-135); the sweep makes at most `n(n+1)`
moves and ends at the colouring in which every vertex is greedy (l. 164-165); a neighbour of a cone vertex outside the
cone is an out-neighbour (l. 260-261); a cone vertex other than `v_t` keeps two more colours than it has
out-neighbours in the cone (l. 261-262).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Basic
import Cereceda.Defs.Instance
import Cereceda.Setting.Heights
import Cereceda.Setting.Small
import Cereceda.Setting.Sweep
import Cereceda.Setting.CaseAPaperCounts
import Cereceda.Bip.MainV40

namespace Cereceda

open Finset

namespace TextMoves

section Seq

variable {W : Type} [DecidableEq W] (H : SimpleGraph W) (A : W → Finset (Fin 4))

theorem movesOf_cons (ms : List (W × Fin 4)) (m : W × Fin 4) (v : W) :
    movesOf (m :: ms) v = movesOf ms v + (if m.1 = v then 1 else 0) := by
  simp [movesOf, List.countP_cons]

/-- A vertex that never moves keeps its colour. -/
theorem colour_of_movesOf_zero :
    ∀ (ms : List (W × Fin 4)) (c c' : W → Fin 4) (v : W), IsSeq H A c ms c' → movesOf ms v = 0 → c' v = c v
  | [], c, c', v, hs, _ => by rw [show c' = c from hs]
  | m :: ms, c, c', v, hs, h0 => by
    rw [movesOf_cons] at h0
    have hmv : m.1 ≠ v := by intro e; simp [e] at h0
    have h0' : movesOf ms v = 0 := by omega
    rw [colour_of_movesOf_zero ms _ c' v hs.2 h0', Function.update_of_ne (Ne.symm hmv)]

/-- A vertex that moves at most once moves to its final colour. -/
theorem move_to_final :
    ∀ (ms : List (W × Fin 4)) (c c' : W → Fin 4) (v : W), IsSeq H A c ms c' → movesOf ms v ≤ 1 →
      ∀ m ∈ ms, m.1 = v → m.2 = c' v
  | [], _, _, _, _, _, _, hm, _ => by simp at hm
  | m0 :: ms, c, c', v, hs, h1, m, hm, hmv => by
    rw [movesOf_cons] at h1
    rcases List.mem_cons.1 hm with rfl | hm'
    · have hif : (if m.1 = v then 1 else 0) = 1 := by simp [hmv]
      have h0 : movesOf ms v = 0 := by omega
      rw [colour_of_movesOf_zero H A ms _ c' v hs.2 h0, ← hmv, Function.update_self]
    · exact move_to_final ms _ c' v hs.2 (by omega) m hm' hmv

end Seq

/-- No colour of `{1,2,3}` differs from two distinct colours of `{1,2,3}` in two ways (integer form). -/
theorem third_colour {a b p q : ℕ} (ha : 0 < a) (ha4 : a < 4) (hb : 0 < b) (hb4 : b < 4) (hp : 0 < p) (hp4 : p < 4)
    (hq : 0 < q) (hq4 : q < 4) (hab : a ≠ b) (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) : p = q := by
  omega

/-- The cone of `w` has at most `ρ w + 1` vertices, since it lies in `{v_1, …, v_t}` for `w = v_t`. -/
theorem cone_card_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n : ℕ} (ρ : V ≃ Fin n) (w : V) :
    (cone G ρ w).card ≤ (ρ w).val + 1 := by
  classical
  have hsub : cone G ρ w ⊆ (Finset.Iic (ρ w)).map ρ.symm.toEmbedding := by
    intro u hu
    simp only [mem_map_equiv, Equiv.symm_symm, mem_Iic]
    exact le_of_mem_cone hu
  refine (card_le_card hsub).trans ?_
  simp

end TextMoves

open TextMoves

/-- Section 2, v4.24 l. 303-304: "A move changes the current height function by `±2` at the moved vertex only. (In a
`3`-colouring of a tree, a vertex can be recoloured only when all its neighbours have the same colour, and then its
height changes by `±2`.)" Stated for any graph `T` (not only trees): if `c` uses the colours `1, 2, 3`, `h` is a height
of `c` and the move `(v, y)` with the lists `{1,2,3}` is legal, then all neighbours of `v` have the same colour, and
some height of the new colouring differs from `h` by `±2` at `v` and agrees with `h` elsewhere. -/
theorem sec2_tree_move_proved {W : Type} [DecidableEq W] (T : SimpleGraph W) (c : W → Fin 4)
    (hc : ∀ w, c w ∈ ({1, 2, 3} : Finset (Fin 4))) (h : W → ℤ) (hh : IsHeight T c h) (v : W) (y : Fin 4)
    (hm : LegalMove T (fun _ => ({1, 2, 3} : Finset (Fin 4))) c (v, y)) :
    (∀ u w, T.Adj v u → T.Adj v w → c u = c w) ∧
      ∃ h' : W → ℤ, IsHeight T (Function.update c v y) h' ∧ (h' v = h v + 2 ∨ h' v = h v - 2) ∧
        ∀ u, u ≠ v → h' u = h u := by
  have hH := (Heights.isHeight_iff T c h).1 hh
  obtain ⟨hyv, hyA, hnb⟩ := hm
  simp only at hyv hyA hnb
  have hpos : ∀ w, 0 < (c w).val := fun w => (Heights.mem123_iff _).1 (hc w)
  have hy : 0 < y.val := (Heights.mem123_iff _).1 hyA
  have hyv' : y.val ≠ (c v).val := fun e => hyv (Fin.ext e)
  -- a neighbour of `v` is on neither `c v` (heights differ by one) nor `y` (the move is legal)
  have hnv : ∀ u, T.Adj v u → (c u).val ≠ (c v).val := by
    intro u hu e
    have h1 := hH.1 u
    have h2 := hH.1 v
    rcases hH.2 v u hu with h3 | h3 <;> omega
  have hny : ∀ u, T.Adj v u → (c u).val ≠ y.val := fun u hu e => hnb u hu (Fin.ext e)
  refine ⟨fun u w hu hw => Fin.ext (third_colour (hpos v) (c v).isLt hy y.isLt (hpos u) (c u).isLt (hpos w)
    (c w).isLt (Ne.symm hyv') (hnv u hu) (hny u hu) (hnv w hw) (hny w hw)), ?_⟩
  -- the sign `d` with `h v + 2d ≡ y (mod 3)`
  obtain ⟨d, hd, hdy⟩ : ∃ d : ℤ, (d = 1 ∨ d = -1) ∧ (3 : ℤ) ∣ h v + 2 * d - y.val := by
    have h1 := hH.1 v
    have := (c v).isLt
    have := y.isLt
    have := hpos v
    by_cases h2 : (3 : ℤ) ∣ h v + 2 * 1 - y.val
    · exact ⟨1, Or.inl rfl, h2⟩
    · exact ⟨-1, Or.inr rfl, by omega⟩
  -- every neighbour `u` of `v` has `h u = h v + d`; otherwise `u` would be on `y`
  have hnbd : ∀ u, T.Adj v u → h u = h v + d := by
    intro u hu
    have h1 := hH.1 u
    have := (c u).isLt
    have := y.isLt
    have := hpos u
    have := hny u hu
    rcases hH.2 v u hu with h3 | h3 <;> rcases hd with rfl | rfl <;> omega
  refine ⟨Function.update h v (h v + 2 * d),
    (Heights.isHeight_iff T _ _).2 (Heights.step_hh hH hd hnbd hdy), ?_, fun u hu => Function.update_of_ne hu _ _⟩
  rw [Function.update_self]
  rcases hd with rfl | rfl
  · exact Or.inl (by ring)
  · exact Or.inr (by ring)

/-- Lemma 2.4, v4.24 l. 316-317: "The condition on `E(r)` makes `r`, which may have fewer than three allowed colours,
move at most once, and then directly to `c'(r)`." With the hypotheses of Lemma 2.4 (`lem_2_4`) and `|P| ≤ 2`, the
sequence of Lemma 2.4 moves every vertex `v` exactly `|E v|/2` times, moves `r` at most once, and every move of `r`
goes to `c'(r)`. -/
theorem lem_2_4_root_once_proved {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) (hT : T.IsTree) (r : W)
    (P : Finset (Fin 4)) (hP : P ⊆ {1, 2, 3}) (c c' : W → Fin 4) (hc : IsProperFn T c) (hc' : IsProperFn T c')
    (hcA : ∀ v, c v ∈ treeLists r P v) (hc'A : ∀ v, c' v ∈ treeLists r P v)
    (h E : W → ℤ) (hh : IsHeight T c h) (hE : ∀ v, Even (E v)) (hhE : IsHeight T c' (h + E))
    (hr : P.card ≤ 2 → |E r| ≤ 2) (hP2 : P.card ≤ 2) :
    ∃ ms, IsSeq T (treeLists r P) c ms c' ∧ (∀ v, 2 * movesOf ms v = (E v).natAbs) ∧ movesOf ms r ≤ 1 ∧
      ∀ m ∈ ms, m.1 = r → m.2 = c' r := by
  obtain ⟨ms, hs, -, hmv⟩ := lem_2_4_proved T hT r P hP c c' hc hc' hcA hc'A h E hh hE hhE hr
  have h1 : movesOf ms r ≤ 1 := by
    have h2 := hmv r
    obtain ⟨h3, h4⟩ := abs_le.1 (hr hP2)
    omega
  exact ⟨ms, hs, hmv, h1, move_to_final T _ ms c c' r hs h1⟩

/-- Section 1 (outline), v4.24 l. 134-135: "Since no vertex outside the cone has a later neighbour in it, recolouring
the cone cannot make a vertex outside it non-greedy." No later neighbour of a vertex outside the cone of `w` lies in
the cone; and if two colourings agree outside the cone, a vertex outside the cone that is greedy (has the least colour
that none of its later neighbours has) in the first is greedy in the second. The first part is also the reason in
Section 2, l. 260-261: "A vertex of `C_t` has no other neighbours outside `C_t`, since a vertex with an arc into `C_t`
lies in `C_t`" (the claim itself: `sec2_cone_outside_nbrs_proved`). -/
theorem intro_outside_cone_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (ρ : V ≃ Fin n) (w : V) :
    (∀ u, u ∉ cone G ρ w → ∀ v ∈ laterNbrs G ρ u, v ∉ cone G ρ w) ∧
    ∀ c d : V → Fin 4, (∀ v, v ∉ cone G ρ w → d v = c v) → ∀ u, u ∉ cone G ρ w →
      IsLeastFree Finset.univ ((laterNbrs G ρ u).image c) (c u) →
        IsLeastFree Finset.univ ((laterNbrs G ρ u).image d) (d u) := by
  have hout : ∀ u, u ∉ cone G ρ w → ∀ v ∈ laterNbrs G ρ u, v ∉ cone G ρ w := by
    intro u hu v hv hvc
    have hv' := Sweep.mem_laterNbrs.1 hv
    exact hu (Sweep.mem_cone_of_arc hv'.1 hv'.2 hvc (hv'.2.le.trans (le_of_mem_cone hvc)))
  refine ⟨hout, fun c d hd u hu hgr => ?_⟩
  have himg : (laterNbrs G ρ u).image d = (laterNbrs G ρ u).image c :=
    image_congr (fun v hv => hd v (hout u hu v (mem_coe.1 hv)))
  rw [himg, hd u hu]
  exact hgr

/-- Section 2, v4.24 l. 260-261: "A vertex of `C_t` has no other neighbours outside `C_t`, since a vertex with an arc
into `C_t` lies in `C_t`." A vertex with an arc into the cone of `w` lies in the cone (`Sweep.mem_cone_of_arc`), so a
neighbour of a cone vertex outside the cone is one of its later neighbours (`Sweep.lt_of_adj_mem_cone`). -/
theorem sec2_cone_outside_nbrs_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (ρ : V ≃ Fin n) (w : V) :
    (∀ a b, Arc G ρ a b → b ∈ cone G ρ w → a ∈ cone G ρ w) ∧
    ∀ u ∈ cone G ρ w, ∀ v, G.Adj u v → v ∉ cone G ρ w → v ∈ laterNbrs G ρ u := by
  refine ⟨fun a b hab hb => ?_, fun u hu v huv hv => ?_⟩
  · obtain ⟨hadj, hlt⟩ := hab
    exact Sweep.mem_cone_of_arc hadj hlt hb (hlt.le.trans (le_of_mem_cone hb))
  · exact Sweep.mem_laterNbrs.2 ⟨huv, Sweep.lt_of_adj_mem_cone huv hu hv⟩

/-- Section 2, v4.24 l. 261-262: "As every vertex has at most two out-neighbours and there are four colours, every
vertex of `C_t` other than `v_t` keeps at least two more colours than it has out-neighbours inside `C_t`." The colours
kept are those of no later neighbour outside the cone of `w` (`w = v_t`). Read off from `Sweep.coneL_card`, the list
condition of the cone instance in the proof of Lemma 2.5: the list of a vertex `u ≠ w` is this set, and the
out-neighbours of `u` in the instance are its later neighbours in the cone. -/
theorem sec2_cone_lists_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (ρ : V ≃ Fin n) (hρ : IsDegOrder G 2 ρ) (w : V) (c : V → Fin 4) (u : V) (hu : u ∈ cone G ρ w)
    (huw : u ≠ w) :
    ((laterNbrs G ρ u).filter (fun v => v ∈ cone G ρ w)).card + 2 ≤
      ((((laterNbrs G ρ u).filter (fun v => v ∉ cone G ρ w)).image c)ᶜ).card := by
  -- the target colour `g` enters only the list of `w`; any `g ≠ c w` will do
  obtain ⟨g, hg⟩ : ∃ g : Fin 4, g ≠ c w := by
    by_cases h0 : c w = 0
    · exact ⟨1, by rw [h0]; decide⟩
    · exact ⟨0, fun h => h0 h.symm⟩
  have hcard := Sweep.coneL_card hρ w c g hg ⟨u, hu⟩
  have hL : Sweep.coneL G ρ w c g ⟨u, hu⟩ =
      (((laterNbrs G ρ u).filter (fun v => v ∉ cone G ρ w)).image c)ᶜ := by
    simp only [Sweep.coneL, Sweep.outNbrs, huw, ite_false]
  have hout : ((laterNbrs G ρ u).filter (fun v => v ∈ cone G ρ w)).card ≤
      ((coneSkeleton G ρ hρ w).out ⟨u, hu⟩).card := by
    refine card_le_card_of_surjOn Subtype.val ?_
    intro v hv
    have hv' := mem_filter.1 (mem_coe.1 hv)
    exact ⟨⟨v, hv'.2⟩, mem_coe.2 (Sweep.mem_out.2 (Sweep.mem_laterNbrs.1 hv'.1)), rfl⟩
  rw [hL] at hcard
  omega

/-- Section 1 (outline), v4.24 l. 164-165: "As the cone of `v_t` has at most `t` vertices, the sweep makes at most
`2(1 + 2 + ⋯ + n) = n(n+1)` moves. It ends at the colouring in which every vertex is greedy." For a bipartite `G`
with a degeneracy ordering `ρ` (`ρ v_t = t - 1`): `|C_t| ≤ t`, `2 ∑_t |C_t| ≤ n(n+1)`, and from every colouring the
sweep (Lemma 2.5 with `λ = 2` and Theorem 3.1 in every cone) reaches, within `n(n+1)` moves, a colouring in which every
vertex is greedy. -/
theorem intro_sweep_total_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (ρ : V ≃ Fin n) (hbip : G.IsBipartite) (hρ : IsDegOrder G 2 ρ) :
    (∀ w, (cone G ρ w).card ≤ (ρ w).val + 1) ∧ 2 * ∑ w, (cone G ρ w).card ≤ n * (n + 1) ∧
    ∀ c : V → Fin 4, IsProperFn G c → ∃ ms c', IsSeq G (fun _ => Finset.univ) c ms c' ∧ ms.length ≤ n * (n + 1) ∧
      ∀ u, IsLeastFree Finset.univ ((laterNbrs G ρ u).image c') (c' u) := by
  have hsum := (def_2_1_cones_proved G ρ).2.2
  refine ⟨cone_card_le G ρ, hsum, fun c hc => ?_⟩
  obtain ⟨ms, c', hs, hl, hgr⟩ := Sweep.sweep_upto (fun W _ _ S => S.NoRoots ∧ S.graph.IsBipartite) 2 le_rfl
    (by
      intro W _ _ I hI _ α β hα hβ
      obtain ⟨ms, hms, -, -, hlen⟩ := thm_3_1_of_v40 sec3_caseA_counts_paper_proved I hI.1 hI.2 α β hα hβ
      refine ⟨ms, hms, ?_⟩
      have : ms.length ≤ 2 * Fintype.card W := hlen.trans (Nat.sub_le _ _)
      exact_mod_cast this)
    hρ (fun w => ⟨(thm_1_2_cones_proved G hbip ρ hρ w).2, (thm_1_2_cones_proved G hbip ρ hρ w).1⟩)
    n le_rfl c hc
  refine ⟨ms, c', hs, ?_, fun u => hgr u (ρ u).isLt⟩
  rw [Sweep.sum_coneSize] at hl
  have h' : 2 * ∑ w, ((cone G ρ w).card : ℝ) ≤ (n : ℝ) * (n + 1) := by exact_mod_cast hsum
  have h'' : (ms.length : ℝ) ≤ (n : ℝ) * (n + 1) := hl.trans h'
  exact_mod_cast h''

end Cereceda
