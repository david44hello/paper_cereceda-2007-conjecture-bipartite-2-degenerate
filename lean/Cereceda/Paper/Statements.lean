/-
Cereceda/Paper/Statements.lean — one theorem per claim of the paper
"The Cereceda (2007) conjecture holds for bipartite 2-degenerate graphs" (Dave Goel).
This file cites short version v4.24 (short_v4.24.tex, md5 901648f6).
PAPER VERSION: v4.24
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Each docstring names the paper's statement number and the lines of short_v4.24.tex (line numbers as printed by
`cat -n`) that state the claim: "v4.24 l. N" (or "l. N-M", "l. N and M"). Text in double quotes is v4.24 word for word
(LaTeX simplified to Unicode or backticks).
Section 4: Lean's `n` is the paper's ℓ (the number of path vertices); the paper's `n` is the number of vertices.
Indexing in Section 4: `Sum.inl i` is the paper's `v_{i+1}`.
-/
import Cereceda.Defs.Basic
import Cereceda.Defs.Instance
import Cereceda.Defs.Bipartite
import Cereceda.Defs.LowerBound
import Cereceda.Defs.Intro
import Cereceda.Cited.Cer07
import Cereceda.Bip.MainV40
import Cereceda.Bip.Example8Three
import Cereceda.Setting.CaseAPaper
import Cereceda.Setting.CaseAPaperCounts
import Cereceda.Defs.Example8
import Cereceda.LB.Cost
import Cereceda.Setting.Small
import Cereceda.Setting.Assembly
import Cereceda.Setting.Heights
import Cereceda.Setting.Degeneracy
import Cereceda.Setting.CaseA
import Cereceda.Setting.Sweep
import Cereceda.Intro.Examples
import Cereceda.Setting.Misc
import Cereceda.Intro.Subdivision
import Cereceda.Intro.Classes
import Cereceda.Intro.Connected
import Cereceda.Setting.SweepSteps
import Cereceda.Bip.Counts
import Cereceda.Bip.MuV40
import Cereceda.Bip.Example8
import Cereceda.LB.Sec4
import Cereceda.LB.LowerBounds
import Cereceda.LB.PathHeight
import Cereceda.Setting.HeightExtend
import Cereceda.Defs.Triangle
import Cereceda.Defs.Classes
import Cereceda.Bip.Triangle
import Cereceda.Intro.SemiFalse
import Cereceda.Intro.DistanceHereditary
import Cereceda.Defs.ColourDense
import Cereceda.Defs.OAT
import Cereceda.Cited.BJLPP14
import Cereceda.Cited.BH22
import Cereceda.Intro.ColourDense
import Cereceda.Intro.OAT
import Cereceda.Intro.SemiFalseIII
import Cereceda.Intro.TextSteps
import Cereceda.Setting.CaseASteps
import Cereceda.LB.GirthSteps
import Cereceda.Setting.ZeroFull
import Cereceda.Defs.Minor
import Cereceda.Defs.Degeneracy
import Cereceda.Setting.DegeneracyForm
import Cereceda.LB.JMinor
import Cereceda.LB.JDegrees
import Cereceda.LB.JNotDense
import Cereceda.LB.NamedCycles
import Cereceda.Defs.PathClique
import Cereceda.Defs.Example2
import Cereceda.Intro.PathClique
import Cereceda.Intro.ChordalKmn
import Cereceda.Setting.TextMoves
import Cereceda.Bip.TextCounts
import Cereceda.LB.TextApex

namespace Cereceda

open Finset

/-! ## Section 1 — Introduction -/

/-- Conjecture 1.1 (Cereceda), v4.24 l. 72-75 (= [Cer07, Conj. 5.21]). A DEFINITION of the open statement
(it is NOT claimed): for every `d ≥ 1` and every `k ≥ d + 2` there is `C` with `diam R_k(G) ≤ C n²` for every
`d`-degenerate `G` on `n` vertices. -/
def CerecedaConjecture : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, d + 2 ≤ k → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], IsDegenerate G d → (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞)

/-- The conjecture for one `d` and a class `Cls` of graphs (a DEFINITION): for every `k ≥ d + 2` there
is `C` with `diam R_k(G) ≤ C n²` for every `d`-degenerate `G` of the class. `cerecedaConjecture_iff_on`: the
conjecture is this statement for every `d ≥ 1` and the class of all graphs. -/
def CerecedaConjectureOn (Cls : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], Prop)
    (d : ℕ) : Prop :=
  ∀ k : ℕ, d + 2 ≤ k → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], Cls V G → IsDegenerate G d → (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞)

/-- The class of all finite graphs. -/
def AllGraphs (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop := True

/-- The class of the paper: bipartite graphs of degeneracy at most `2`. -/
def BipTwoDegenerate (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.IsBipartite ∧ IsDegenerate G 2

/-- Sanity check of `CerecedaConjectureOn`: Conjecture 1.1 is `CerecedaConjectureOn AllGraphs d` for every `d ≥ 1`. -/
theorem cerecedaConjecture_iff_on : CerecedaConjecture ↔ ∀ d : ℕ, 1 ≤ d → CerecedaConjectureOn AllGraphs d := by
  constructor
  · intro h d hd k hk
    obtain ⟨C, hC⟩ := h d hd k hk
    exact ⟨C, by intro V _ _ G _ _ hG; exact hC V G hG⟩
  · intro h d hd k hk
    obtain ⟨C, hC⟩ := h d hd k hk
    exact ⟨C, by intro V _ _ G _ hG; exact hC V G True.intro hG⟩

/-- Faithfulness of `degeneracy` (Defs/Degeneracy.lean; v4.24 l. 64-65, "The degeneracy of a graph is the least `d` for
which it is `d`-degenerate"): `G` is `degeneracy G`-degenerate, and `degeneracy G ≤ d` whenever `G` is `d`-degenerate. -/
theorem degeneracy_spec {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsDegenerate G (degeneracy G) ∧ ∀ d, IsDegenerate G d → degeneracy G ≤ d :=
  ⟨isDegenerate_degeneracy G, fun _ h => degeneracy_le G h⟩

/-- Section 1, v4.24 l. 77 (the reason for `conj_1_1_forms_equivalent`): "a `d`-degenerate graph with an edge has
degeneracy between `1` and `d`". -/
theorem conj_1_1_degeneracy_between {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (he : ∃ u v, G.Adj u v) (h : IsDegenerate G d) : 1 ≤ degeneracy G ∧ degeneracy G ≤ d :=
  degeneracy_between G he h

/-- Section 1, v4.24 l. 76-78: "Cereceda states it with `d` equal to the degeneracy of `G`. The two forms are equivalent
for graphs with at least one edge, since a `d`-degenerate graph with an edge has degeneracy between `1` and `d`, and we can
take for `C` the largest of the constants that Cereceda's form gives for these degeneracies and the same `k`." Left:
Conjecture 1.1 for the graphs with at least one edge; right: the same with `degeneracy G = d` (`degeneracy`,
Defs/Degeneracy.lean) in place of `IsDegenerate G d`. The Lean proof takes the largest of these constants for the
same `k`, as the paper (Setting/DegeneracyForm.lean). -/
theorem conj_1_1_forms_equivalent :
    (∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, d + 2 ≤ k → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], (∃ u v, G.Adj u v) → IsDegenerate G d →
        (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞)) ↔
    (∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, d + 2 ≤ k → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], (∃ u v, G.Adj u v) → degeneracy G = d →
        (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞)) :=
  conj_forms_equiv_edge

/-- Conjecture 1.1 in Cereceda's form, a DEFINITION (it is NOT claimed): `CerecedaConjecture` with
`degeneracy G = d` (`degeneracy`) in place of `IsDegenerate G d`. -/
def CerecedaConjectureDegeneracy : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, d + 2 ≤ k → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], degeneracy G = d → (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞)

/-- Sanity check, beyond the paper's sentence (which is `conj_1_1_forms_equivalent`): the two forms of Conjecture 1.1
are also equivalent for all graphs. Graphs without edges have degeneracy `0`, which Cereceda's form (`d ≥ 1`) does not
cover; for them `diam R_k(G) ≤ n` (`ediam_le_card_of_edgeless`, proved directly, no citation). -/
theorem conj_1_1_forms_all_graphs : CerecedaConjecture ↔ CerecedaConjectureDegeneracy :=
  conj_forms_equiv

/-- Section 1, v4.24 l. 65: a `d`-degenerate graph has a proper `(d+1)`-colouring. -/
theorem intro_degenerate_colorable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) (hd : IsDegenerate G d) : G.Colorable (d + 1) := by
  exact intro_degenerate_colorable_proved G d hd

/-- Section 1, v4.24 l. 67-68: for `k = d + 1` the graph `R_k(G)` can be disconnected (`G = K_{d+1}`, which is
`d`-degenerate). -/
theorem intro_complete_disconnected (d : ℕ) (hd : 1 ≤ d) :
    IsDegenerate (⊤ : SimpleGraph (Fin (d + 1))) d ∧
      ¬ (recolGraph (⊤ : SimpleGraph (Fin (d + 1))) (d + 1)).Connected := by
  exact intro_complete_disconnected_proved d hd

/-- Section 1, v4.24 l. 221-224: "Class (iv) contains many bipartite `2`-degenerate graphs, for example every graph
obtained from a graph by subdividing each of its edges once": once-subdivided graphs are bipartite and `2`-degenerate and
have Grundy number at most `3` (in a first-fit colouring a subdivision vertex gets colour 3 only after both of its
neighbours, so no original vertex gets colour 4; l. 222-224). -/
theorem intro_subdivision {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (subdivision G).IsBipartite ∧ IsDegenerate (subdivision G) 2 ∧ grundyNumber (subdivision G) ≤ 3 := by
  exact intro_subdivision_proved G

/-- Section 1, v4.24 l. 65-67 (stated there with citations to [DFFV06], [CvdHJ08] and [Cer07, Thm. 2.7]; proved
here): for a `d`-degenerate graph and
`k ≥ d + 2` the recolouring graph `R_k(G)` is connected. -/
theorem intro_connected {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d k : ℕ)
    (hk : d + 2 ≤ k) (hd : IsDegenerate G d) : (recolGraph G k).Connected := by
  exact intro_connected_proved G d k hk hd

/-- Section 1 and Remark 4.9, v4.24 l. 227-229 and 795-797: a distance-hereditary graph is "a graph in which any two
vertices of a connected induced subgraph are at the same distance in the subgraph as in the whole graph" (Section 1,
l. 228-229; `IsDistanceHereditary`), and "A bipartite distance-hereditary graph has no induced cycle of length at least
`6`, since deleting one vertex of such a cycle would leave a connected induced path whose ends are at distance `2` in the
graph but at least `4` in the path. Being chordal bipartite" (Remark 4.9, l. 795-797; chordal bipartite graphs are
defined at l. 794-795, `IsChordalBipartite`). The paper's next words, "it is semi-false and lies in (iii)" (l. 797-798), are the
row `intro_dh_in_iii`. -/
theorem intro_dh_chordal_bipartite {V : Type} (G : SimpleGraph V) (hbip : G.IsBipartite)
    (hdh : IsDistanceHereditary G) : IsChordalBipartite G :=
  intro_dh_chordal_bipartite_proved G hbip hdh

/-! ### Section 1 and Remark 4.9, v4.24: class (iii) (3-colour-dense graphs, defined in Remark 4.8) and the classes
that land in it (the witness `J_ℓ` that lies in none of (i)-(v) is Remark 4.8, rows at the end of Section 4) -/

/-- Section 1, v4.24 l. 213-215 (after the list; used for class (ii)): the hypothesis of [BFHR25, Thm. 1.3] holds,
"This holds for every non-empty `2`-degenerate graph, since such a graph has a vertex of degree at most `2`,
and with four colours such a vertex can always be recoloured" (recoloured = an edge of `R_4(G)` that changes only that vertex; on a
nonempty graph, `Nonempty V`: the empty graph has no vertex). -/
theorem intro_low_degree_recolour {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (hd : IsDegenerate G 2) :
    (∃ v, G.degree v ≤ 2) ∧ ∀ (c : G.Coloring (Fin 4)) (v : V), G.degree v ≤ 2 →
      ∃ c' : G.Coloring (Fin 4), (recolGraph G 4).Adj c c' ∧ ∀ w, w ≠ v → c' w = c w :=
  intro_low_degree_recolour_proved G hd

/-- Section 1, v4.24 l. 207-208, class (iv): the bound `4χ(G)n` of [BB18, Thm. 1]; "for bipartite `G` this is at most
`8n`" (`χ(G) ≤ 2`; Mathlib's `chromaticNumber`, in `ℕ∞`). -/
theorem intro_grundy_bound_bipartite {V : Type} [Fintype V] (G : SimpleGraph V) (hbip : G.IsBipartite) :
    4 * G.chromaticNumber * (Fintype.card V : ℕ∞) ≤ 8 * (Fintype.card V : ℕ∞) := by
  have h : G.chromaticNumber ≤ 2 := SimpleGraph.Colorable.chromaticNumber_le hbip
  calc 4 * G.chromaticNumber * (Fintype.card V : ℕ∞) ≤ 4 * 2 * (Fintype.card V : ℕ∞) := by gcongr
    _ = 8 * (Fintype.card V : ℕ∞) := by norm_num

/-- Remark 4.9, v4.24 l. 790-791: the `2`-colour-dense graphs "are also `3`-colour-dense, by induction on the number of
vertices" (`IsColourDense`, Defs/ColourDense.lean, is the definition of l. 773-778 (Remark 4.8) and 761-762). -/
theorem colourDense_two_three {V : Type} (G : SimpleGraph V) : IsColourDense 2 G → IsColourDense 3 G :=
  colourDense_two_three_proved G

/-- Remark 4.9, v4.24 l. 791-792: "Among the `2`-colour-dense graphs are the semi-false graphs [BJLPP14, Thm. 10]" (cited:
`Cited.bjlpp14_thm10`), so every semi-false graph lies in (iii) (with `colourDense_two_three`; the empty graph directly). -/
theorem intro_semiFalse_in_iii {V : Type} [Fintype V] (G : SimpleGraph V) (h : IsSemiFalse G) : IsColourDense 3 G :=
  intro_semiFalse_in_iii_proved G h

/-- Section 1, v4.24 l. 227-229: [BB18, Thm. 4] needs `k ≥ χ(G) + 1` colours, "including four colours when
`χ(G) ≤ 3`". -/
theorem intro_dh_four_colours {V : Type} (G : SimpleGraph V) (h : G.chromaticNumber ≤ 3) :
    G.chromaticNumber + 1 ≤ 4 :=
  calc G.chromaticNumber + 1 ≤ 3 + 1 := by gcongr
    _ = 4 := by norm_num

/-- Remark 4.9, v4.24 l. 795-798: "A bipartite distance-hereditary graph ... Being chordal bipartite, it is semi-false
and lies in (iii)" (`intro_dh_chordal_bipartite`, then [BJLPP14, Thm. 8] (cited: `Cited.bjlpp14_thm8`), then
`intro_semiFalse_in_iii`). -/
theorem intro_dh_in_iii {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hbip : G.IsBipartite)
    (hdh : IsDistanceHereditary G) : IsColourDense 3 G :=
  intro_dh_in_iii_proved G hbip hdh

/-- Remark 4.9, v4.24 l. 805 (the join of two edgeless graphs, a complete bipartite graph): "So the join is a complete
bipartite graph; it is chordal bipartite and therefore semi-false". -/
theorem intro_completeBipartite_semiFalse (m n : ℕ) : IsSemiFalse (completeBipartiteGraph (Fin m) (Fin n)) :=
  intro_completeBipartite_semiFalse_proved m n

/-- Remark 4.9, v4.24 l. 806: "A disjoint union of two semi-false graphs is semi-false". -/
theorem intro_union_semiFalse {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) : IsSemiFalse G → IsSemiFalse H → IsSemiFalse (G ⊕g H) :=
  intro_union_semiFalse_proved G H

/-- Remark 4.9, v4.24 l. 808: "adding a vertex `u` with `N(u) ⊆ N(v)` keeps a graph semi-false" (`addVertex G S` adds
one vertex adjacent exactly to `S`). -/
theorem intro_addVertex_semiFalse {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V) (S : Set V)
    (hS : S ⊆ G.neighborSet v) : IsSemiFalse G → IsSemiFalse (addVertex G S) :=
  intro_addVertex_semiFalse_proved G v S hS

/-- Remark 4.9, v4.24 l. 802-809: "By induction along the construction, a bipartite OAT graph is semi-false" (`IsOAT`,
Defs/OAT.lean, is the definition of l. 800-802). -/
theorem intro_oat_semiFalse {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : IsOAT G)
    (hbip : G.IsBipartite) : IsSemiFalse G :=
  intro_oat_semiFalse_proved G hG hbip

/-- Remark 4.9, v4.24 l. 802-803 (a step of the OAT argument; the Lean proof of `intro_oat_semiFalse` passes
bipartiteness down along subgraph maps instead, so the step is its own row): "Each operation adds edges only at a new
vertex or between the two graphs that it combines, so every graph built along the way is an induced subgraph of the
final graph": each of the four operations (disjoint union, join, adding a vertex adjacent to `S`, attaching a clique on
`k` vertices to `v`) embeds the graphs it is given as induced subgraphs (`↪g`: adjacency is preserved and reflected), and
such embeddings compose. -/
theorem intro_oat_induced {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (S : Set V) (v : V) (k : ℕ) :
    Nonempty (G ↪g G ⊕g H) ∧ Nonempty (H ↪g G ⊕g H) ∧ Nonempty (G ↪g joinGraph G H) ∧
      Nonempty (H ↪g joinGraph G H) ∧ Nonempty (G ↪g addVertex G S) ∧ Nonempty (G ↪g attachClique G v k) :=
  intro_oat_induced_proved G H S v k

/-- Remark 4.9, v4.24 l. 804-805 (a step of the OAT argument): "So the join is a complete bipartite graph": the join of
two edgeless graphs is the complete bipartite graph on their vertex sets. -/
theorem intro_oat_join_completeBipartite (V W : Type) :
    joinGraph (⊥ : SimpleGraph V) (⊥ : SimpleGraph W) = completeBipartiteGraph V W :=
  (completeBipartite_eq_joinGraph V W).symm

/-- Remark 4.9, v4.24 l. 805 (a step of the OAT argument; Lean proves "semi-false" directly,
`intro_completeBipartite_semiFalse`, so the step is its own row): "So the join is a complete bipartite graph; it is
chordal bipartite": `K_{m,n}` is chordal bipartite (`IsChordalBipartite`, the definition of l. 794-795). -/
theorem rem_4_9_Kmn_chordal (m n : ℕ) : IsChordalBipartite (completeBipartiteGraph (Fin m) (Fin n)) :=
  rem_4_9_Kmn_chordal_proved m n

/-- Remark 4.9, v4.24 l. 803-804: "If the final graph is bipartite, so are all of them": a graph that embeds as an induced
subgraph (`↪g`) of a bipartite graph is bipartite; with `intro_oat_induced` this covers every graph built along the way. -/
theorem rem_4_9_bipartite_down {V W : Type} (G : SimpleGraph V) (K : SimpleGraph W) (φ : G ↪g K)
    (hK : K.IsBipartite) : G.IsBipartite :=
  rem_4_9_bipartite_down_proved G K φ hK

/-- Section 1 and Remark 4.9, v4.24 l. 226, 229-230 and 800-809: the other classes with quadratic bounds "contain no
bipartite graph outside (i)-(v)" (l. 226); for the bipartite OAT graphs (l. 229-230, "By Remark 4.9, the bipartite graphs
in both classes lie in (iii)"): they lie in (iii) (`intro_oat_semiFalse`, then `intro_semiFalse_in_iii`). -/
theorem intro_oat_in_iii {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : IsOAT G)
    (hbip : G.IsBipartite) : IsColourDense 3 G :=
  intro_oat_in_iii_proved G hG hbip

/-- Table 1 and Section 1, v4.24 l. 105 and 112-113: fans ("Take a path and join every vertex of a clique on `d - 1`
vertices to every vertex of the path (for `d = 2`, a fan)", l. 112-113) "are `2`-degenerate but not bipartite" (Table 1,
l. 105; `n ≥ 2` path vertices; the fan is `pathApex n 1`). -/
theorem intro_fans (n : ℕ) (hn : 2 ≤ n) :
    IsDegenerate (pathApex n 1 (fun _ => 0)) 2 ∧ ¬ (pathApex n 1 (fun _ => 0)).IsBipartite := by
  exact intro_fans_proved n hn

/-- Section 1, v4.24 l. 112-113: "Take a path and join every vertex of a clique on `d - 1` vertices to every vertex of
the path (for `d = 2`, a fan). This graph is `d`-degenerate" (`pathClique n (d - 1)`, Defs/PathClique.lean; for
`d = 2` it is the fan `pathApex n 1`). Its `(d+2)`-recolouring graph "has diameter of order `n²`" is cited
([BJLPP14, Thms. 11 and 12], l. 113-114) and used by no proof. -/
theorem intro_path_clique : (∀ n d : ℕ, 1 ≤ d → IsDegenerate (pathClique n (d - 1)) d) ∧
    ∀ n : ℕ, pathClique n 1 = pathApex n 1 (fun _ => 0) :=
  intro_path_clique_proved

/-- Faithfulness of `grundyNumber` (v4.24 l. 219-221, "The Grundy number in (iv) is the largest number of colours that
a first-fit colouring can use"; it is a true maximum, not a junk `sSup`): some order attains it, and no order's
greedy colouring uses more colours. -/
theorem grundyNumber_spec {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ (ρ : V ≃ Fin (Fintype.card V)) (c : V → ℕ), IsGreedyRel G ρ c ∧ (univ.image c).card = grundyNumber G) ∧
    ∀ (ρ : V ≃ Fin (Fintype.card V)) (c : V → ℕ), IsGreedyRel G ρ c → (univ.image c).card ≤ grundyNumber G := by
  exact grundyNumber_spec_proved G

/-- Section 1, v4.24 l. 54-55 and 110-111: Cereceda's range `k ≥ 2d + 1` [Cer07, Thm. 5.22] contains every `k ≥ d + 2` when
`d = 1` ("which covers `d = 1`", l. 111), and for `d = 2` the only `k ≥ d + 2` outside it is `k = 4` ("only the case
`k = 4` is open for `2`-degenerate graphs", l. 55). -/
theorem intro_cereceda_range :
    (∀ k : ℕ, 1 + 2 ≤ k → 2 * 1 + 1 ≤ k) ∧ ∀ k : ℕ, (2 + 2 ≤ k ∧ ¬ 2 * 2 + 1 ≤ k ↔ k = 4) :=
  ⟨fun _ _ => by omega, fun _ => by omega⟩

/-- Section 1, v4.24 l. 110-111 ("which covers `d = 1`"), as a statement about graphs: by [Cer07, Thm. 5.22]
(cited: `Cited.cer07_thm522`) the conjecture holds for `d = 1`, for all graphs and every `k ≥ 3`. -/
theorem intro_settles_d1 : CerecedaConjectureOn AllGraphs 1 := by
  intro k hk
  obtain ⟨C, hC⟩ := Cited.cer07_thm522 1 k (by omega) (by omega)
  exact ⟨C, by intro V _ _ G _ _ hG; exact hC V G hG⟩

/-- Section 1, v4.24 l. 54-55 ("only the case `k = 4` is open for `2`-degenerate graphs"), as a statement about graphs: a bound
`diam R_4(G) ≤ C n²` for all `2`-degenerate graphs gives the conjecture for `d = 2` (every `k ≥ 5` is [Cer07,
Thm. 5.22], cited: `Cited.cer07_thm522`). -/
theorem intro_only_k4_open
    (h4 : ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsDegenerate G 2 → (recolGraph G 4).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞)) :
    CerecedaConjectureOn AllGraphs 2 := by
  intro k hk
  rcases eq_or_lt_of_le hk with rfl | hk5
  · obtain ⟨C, hC⟩ := h4
    exact ⟨C, by intro V _ _ G _ _ hG; exact hC V G hG⟩
  · obtain ⟨C, hC⟩ := Cited.cer07_thm522 2 k (by omega) (by omega)
    exact ⟨C, by intro V _ _ G _ _ hG; exact hC V G hG⟩

/-! ## Section 2 — Setting: orders, cones, instances, and the sweep -/

/-- Faithfulness of the definition `IsDegenerate` (abstract, v4.24 l. 38-39: "A graph is `d`-degenerate if each of its
non-empty subgraphs has a vertex of degree at most `d`"; Section 1, l. 51-52):
it equals the statement for every nonempty subgraph of `G`. -/
theorem degenerate_iff_subgraph {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) :
    IsDegenerate G d ↔ ∀ H : G.Subgraph, H.verts.Nonempty → ∃ v ∈ H.verts, (H.neighborSet v).ncard ≤ d := by
  exact degenerate_iff_subgraph_proved G d

/-- Section 2, v4.24 l. 246-247: a degeneracy ordering (every vertex has at most two later neighbours) exists: "Since
`G` is `2`-degenerate, we obtain such an ordering by repeatedly deleting a vertex of degree at most `2` and listing the
vertices in the order of deletion". -/
theorem sec2_degeneracy_ordering {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : IsDegenerate G 2) : ∃ ρ : V ≃ Fin (Fintype.card V), IsDegOrder G 2 ρ :=
  (sec2_order_iff_degenerate_proved G 2).2 hd

/-- Definition 2.1 (cones), v4.24 l. 253-256: `v_t ∈ C_t`, `C_t ⊆ {v_1, …, v_t}`, and `∑_t |C_t| ≤ 1 + 2 + ⋯ + n`. -/
theorem def_2_1_cones {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n : ℕ} (ρ : V ≃ Fin n) :
    (∀ w, w ∈ cone G ρ w) ∧ (∀ w u, u ∈ cone G ρ w → ρ u ≤ ρ w) ∧
      2 * ∑ w, (cone G ρ w).card ≤ n * (n + 1) := by
  exact def_2_1_cones_proved G ρ

/-- Section 1, v4.24 l. 134-135: "Since no vertex outside the cone has a later neighbour in it, recolouring the cone
cannot make a vertex outside it non-greedy" (greedy, l. 130: the least colour that none of its later neighbours has).
Section 2, v4.24 l. 260-261: "A vertex of `C_t` has no other neighbours outside `C_t`, since a vertex with an arc into `C_t`
lies in `C_t`": the first part is the reason (no vertex outside the cone has a later neighbour in it); every edge is
an arc one way, so a neighbour of a cone vertex outside the cone is one of its out-neighbours (row
`sec2_cone_outside_nbrs`). -/
theorem intro_outside_cone {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (ρ : V ≃ Fin n) (w : V) :
    (∀ u, u ∉ cone G ρ w → ∀ v ∈ laterNbrs G ρ u, v ∉ cone G ρ w) ∧
    ∀ c d : V → Fin 4, (∀ v, v ∉ cone G ρ w → d v = c v) → ∀ u, u ∉ cone G ρ w →
      IsLeastFree Finset.univ ((laterNbrs G ρ u).image c) (c u) →
        IsLeastFree Finset.univ ((laterNbrs G ρ u).image d) (d u) :=
  intro_outside_cone_proved G ρ w

/-- Section 2, v4.24 l. 260-261: "A vertex of `C_t` has no other neighbours outside `C_t`, since a vertex with an arc
into `C_t` lies in `C_t`." The second part is the claim: a neighbour of a vertex of `C_t` that lies outside `C_t` is
one of its out-neighbours ("its out-neighbours outside `C_t`", l. 259); the first part is the reason (an arc goes to a
later neighbour, `Arc`). `w = v_t`; any order `ρ`. -/
theorem sec2_cone_outside_nbrs {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (ρ : V ≃ Fin n) (w : V) :
    (∀ a b, Arc G ρ a b → b ∈ cone G ρ w → a ∈ cone G ρ w) ∧
    ∀ u ∈ cone G ρ w, ∀ v, G.Adj u v → v ∉ cone G ρ w → v ∈ laterNbrs G ρ u :=
  sec2_cone_outside_nbrs_proved G ρ w

/-- Section 2, v4.24 l. 261-262: "As every vertex has at most two out-neighbours and there are four colours, every
vertex of `C_t` other than `v_t` keeps at least two more colours than it has out-neighbours inside `C_t`." The colours
a vertex keeps are those its out-neighbours outside `C_t` do not have (l. 259: "a vertex of `C_t` may not use the
colours of its out-neighbours outside `C_t`"); `w = v_t`, and the out-neighbours of `u` are its later neighbours. In
the proof of Lemma 2.5 this is the list condition of the cone instance (`Sweep.coneL_card`). -/
theorem sec2_cone_lists {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (ρ : V ≃ Fin n) (hρ : IsDegOrder G 2 ρ) (w : V) (c : V → Fin 4) (u : V) (hu : u ∈ cone G ρ w)
    (huw : u ≠ w) :
    ((laterNbrs G ρ u).filter (fun v => v ∈ cone G ρ w)).card + 2 ≤
      ((((laterNbrs G ρ u).filter (fun v => v ∉ cone G ρ w)).image c)ᶜ).card :=
  sec2_cone_lists_proved G ρ hρ w c u hu huw

/-- Section 1, v4.24 l. 164-165: "As the cone of `v_t` has at most `t` vertices, the sweep makes at most
`2(1 + 2 + ⋯ + n) = n(n+1)` moves. It ends at the colouring in which every vertex is greedy." (`G` bipartite with a
degeneracy ordering `ρ`, `ρ v_t = t - 1`.) -/
theorem intro_sweep_total {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (ρ : V ≃ Fin n) (hbip : G.IsBipartite) (hρ : IsDegOrder G 2 ρ) :
    (∀ w, (cone G ρ w).card ≤ (ρ w).val + 1) ∧ 2 * ∑ w, (cone G ρ w).card ≤ n * (n + 1) ∧
    ∀ c : V → Fin 4, IsProperFn G c → ∃ ms c', IsSeq G (fun _ => Finset.univ) c ms c' ∧ ms.length ≤ n * (n + 1) ∧
      ∀ u, IsLeastFree Finset.univ ((laterNbrs G ρ u).image c') (c' u) :=
  intro_sweep_total_proved G ρ hbip hρ

/-- Definition 2.1 (cones), v4.24 l. 253-254: "the cone `C_t` is the set of vertices from which `v_t` can be reached
along a directed path of arcs, including `v_t` itself" (`Relation.ReflTransGen`: zero or more arcs); Lean's `cone` is
this set. -/
theorem def_2_1_cone_reach {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n : ℕ} (ρ : V ≃ Fin n)
    (w u : V) : u ∈ cone G ρ w ↔ Relation.ReflTransGen (Arc G ρ) u w := by
  exact def_2_1_cone_reach_proved G ρ w u

/-- Definition 2.2 (instances), v4.24 l. 270: "single-sink" ("`s` is its only vertex without out-neighbours") is the
hypothesis `NoRoots` (no vertex other than the sink without out-neighbours) of Theorem 3.1, Lemmas 3.5, 3.6 and
Proposition 3.8. -/
theorem def_2_2_singleSink_iff {W : Type} [Fintype W] [DecidableEq W] (S : Skeleton W) :
    S.IsSingleSink ↔ S.NoRoots := by
  constructor
  · rintro h v ⟨hne, hv⟩
    exact hne (h v hv)
  · intro h v hv
    by_contra hne
    exact h v ⟨hne, hv⟩

/-- Definition 2.2 (instances), v4.24 l. 275-279: the greedy colouring with a given sink colour exists and is
unique; so `α` and `β` "depend only on the out-neighbours and the lists, not on the instance order" (l. 278-279; the
predicate `IsGreedy` does not mention `rank`, Lean's instance order). -/
theorem def_2_2_greedy {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (c0 : Fin 4) :
    ∃! c, I.IsGreedy c0 c := by
  exact def_2_2_greedy_proved I c0

/-- Definition 2.2, v4.24 l. 279: `α` and `β` "are proper, since every vertex avoids the colours of its out-neighbours"
(for any greedy colouring, on the instance graph). -/
theorem def_2_2_greedy_proper {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (c0 : Fin 4) (c : W → Fin 4)
    (hc : I.IsGreedy c0 c) : IsProperFn I.graph c :=
  fun _ _ h => CaseA.greedy_proper hc h

/-- Definition 2.2 (sequences, v4.24 l. 280-281: a move takes a colour of the list that no neighbour has): every
intermediate colouring of a sequence that starts from a proper colouring
within the lists is proper and within the lists. -/
theorem def_2_2_seq_proper {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) (A : W → Finset (Fin 4))
    (c c' : W → Fin 4) (ms : List (W × Fin 4)) (hs : IsSeq H A c ms c') (hc : IsProperFn H c)
    (hA : ∀ v, c v ∈ A v) (k : ℕ) :
    IsProperFn H (applyMoves c (ms.take k)) ∧ ∀ v, applyMoves c (ms.take k) v ∈ A v := by
  exact def_2_2_seq_proper_proved H A c c' ms hs hc hA k

/-- Before Lemma 2.4, v4.24 l. 298-301: on a tree a height of a proper colouring with colours in `{1,2,3}` exists. -/
theorem height_exists {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) (hT : T.IsTree)
    (c : W → Fin 4) (hc : IsProperFn T c) (h0 : ∀ v, c v ≠ 0) : ∃ h, IsHeight T c h := by
  exact height_exists_proved T hT c hc h0

/-- Before Lemma 2.4, v4.24 l. 301: a height is unique up to an additive constant in `3ℤ` (on a connected
graph, so on a tree). -/
theorem height_unique {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) (hT : T.Connected)
    (c : W → Fin 4) (h h' : W → ℤ) (hh : IsHeight T c h) (hh' : IsHeight T c h') :
    ∃ k : ℤ, ∀ v, h' v = h v + 3 * k := by
  exact height_unique_proved T hT c h h' hh hh'

/-- Lemma 2.3 (lem:caseA), v4.24 l. 292-295, first part: in an instance whose sink has
the list `{g, x}` with `0 < g < x` there is a sequence from `α` to `β` of at most `2m` moves, `m` the number of
vertices. The whole statement (also: the sink moves exactly once, every other vertex at most twice) is
`lem_2_3_full` below; it needs the steps of the proof. -/
theorem lem_2_3 {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    ∃ ms, I.IsSeq α ms β ∧ ms.length ≤ 2 * Fintype.card W := by
  exact lem_2_3_proved I hg α β hα hβ

/-- Proof of Lemma 2.3, v4.24 l. 334-336 (case `0 < g`): `K = α⁻¹(0) = β⁻¹(0)` (the paper names this set `U`). -/
theorem lem_2_3_K {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) : ∀ v, α v = 0 ↔ β v = 0 := by
  exact lem_2_3_K_proved I hg α β hα hβ

/-- Proof of Lemma 2.3, v4.24 l. 336-337: "This rule also shows that the colour `0` is full in `α` and in `β`, that is,
every vertex whose list contains `0` is on `0` or has an out-neighbour on `0`" (for any greedy colouring of an instance with `0 < g`). -/
theorem lem_2_3_zero_full {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g) (c0 : Fin 4)
    (c : W → Fin 4) (hc : I.IsGreedy c0 c) (v : W) (hv : (0 : Fin 4) ∈ I.L v) : c v = 0 ∨ ∃ u ∈ I.out v, c u = 0 :=
  lem_2_3_zero_full_proved I hg c0 c hc v hv

/-- Proof of Lemma 2.3, v4.24 l. 337 ("Let `F` be the set of the other vertices"): `F` and its graph are the same for `α`
and `β` (so `lem_2_3_height_extend`, stated for `I.fGraph α`, applies to `β` too). -/
theorem lem_2_3_fGraph_eq {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) : I.fGraph α = I.fGraph β :=
  CaseAPaper.fGraph_eq hg hα hβ

/-- Proof of Lemma 2.3, Claim 1, v4.24 l. 339-341: "Every `v ∈ F` has at most one out-neighbour in `F`" (`F` = the
vertices not on `0`; for the greedy colouring `α`, and in the same way for `β`; `F` is the same set for both by
`lem_2_3_K`). -/
theorem lem_2_3_F1 {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (c0 : Fin 4) (c : W → Fin 4)
    (hc : I.IsGreedy c0 c) (v : W) (hv : c v ≠ 0) : ((I.out v).filter (fun u => c u ≠ 0)).card ≤ 1 := by
  exact lem_2_3_F1_proved I c0 c hc v hv

/-- Proof of Lemma 2.3, Claim 2, v4.24 l. 347-348: "Every vertex `v` of `F` with a parent has `{1,2,3} ⊆ L(v)`" (a
parent of `v` is an out-neighbour of `v` in `F`). -/
theorem lem_2_3_F2 {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (c0 : Fin 4) (c : W → Fin 4)
    (hc : I.IsGreedy c0 c) (v p : W) (hv : c v ≠ 0) (hp : p ∈ I.out v) (hcp : c p ≠ 0) :
    ({1, 2, 3} : Finset (Fin 4)) ⊆ I.L v := by
  exact lem_2_3_F2_proved I c0 c hc v p hv hp hcp

/-- Proof of Lemma 2.3, v4.24 l. 342-343: "Thus `F` induces a forest ..., since on a cycle in `F` the vertex that comes
last in the instance order would have both its neighbours on the cycle as out-neighbours in `F`" (`I.fGraph c` = the graph of `F`). The Lean proof of
Lemma 2.3 does not use this step, so it is its own row. -/
theorem lem_2_3_forest {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (c0 : Fin 4) (c : W → Fin 4)
    (hc : I.IsGreedy c0 c) : (I.fGraph c).IsAcyclic :=
  lem_2_3_forest_proved I c0 c hc

/-- Proof of Lemma 2.3, v4.24 l. 357-359: "Since each vertex has at most one parent, the sink `s` is the only vertex of
`T` without one. Every other vertex of `T` is reached from `s` by passing repeatedly from a vertex to one of its children"
(`T` = the vertices
reachable from the sink in `F`; a parent of `v` = an out-neighbour of `v` in `F`). The paper counts the edges of the tree
`T`; Lean follows a walk in `F` from the sink (the claim is the same). -/
theorem lem_2_3_tree_children {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (c0 : Fin 4)
    (c : W → Fin 4) (hc : I.IsGreedy c0 c) (v : W) (hv : (I.fGraph c).Reachable I.sink v) :
    (v ≠ I.sink → ∃ p ∈ I.out v, c p ≠ 0) ∧
      Relation.ReflTransGen (fun p w => p ∈ I.out w ∧ c p ≠ 0 ∧ c w ≠ 0) I.sink v :=
  lem_2_3_tree_children_proved I c0 c hc v hv

/-- Proof of Lemma 2.3, v4.24 l. 363-365 ("We choose height functions `h_α` of `α|_T` and `h_β` of `β|_T`. Since
`α(s) ≠ β(s)` are colours in `{1,2,3}`, the difference `h_β(s) − h_α(s)` is congruent to `2` or to `−2` modulo `3`.
Shifting `h_β` by a multiple of `3`, we may assume that `E = h_β − h_α` has `E(s) ∈ {−2, 2}`"): such heights exist on
the forest `F` (`I.fGraph α`, the same graph for `β` by `lem_2_3_K`). -/
theorem lem_2_3_heights {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    ∃ hA hB : W → ℤ, IsHeight (I.fGraph α) α hA ∧ IsHeight (I.fGraph α) β hB ∧
      (hB I.sink - hA I.sink = 2 ∨ hB I.sink - hA I.sink = -2) := by
  exact lem_2_3_heights_proved I hg α β hα hβ

/-- Proof of Lemma 2.3, v4.24 l. 363 ("height functions `h_α` of `α|_T` and `h_β` of `β|_T`"): a height of `α` (or
`β`) given only on the tree `T` (the vertices reachable from `s` in `F`) extends to a height on the whole forest `F` that agrees
with it on `T`. So `lem_2_3_offsets`, `lem_2_3_E_bound` and `lem_2_3_paper_route`, stated with heights on `F`, apply to
heights given on `T` (the condition `E(s) ∈ {−2, 2}` is kept, since `s ∈ T`). -/
theorem lem_2_3_height_extend {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (c : W → Fin 4) (hc : c = α ∨ c = β)
    (h : W → ℤ) (hT : (∀ v, (I.fGraph α).Reachable I.sink v → ((h v : ℤ) : ZMod 3) = res (c v)) ∧
      ∀ u v, (I.fGraph α).Reachable I.sink u → (I.fGraph α).Adj u v → |h u - h v| = 1) :
    ∃ h' : W → ℤ, IsHeight (I.fGraph α) c h' ∧ ∀ v, (I.fGraph α).Reachable I.sink v → h' v = h v := by
  obtain ⟨hA, hB, hhA, hhB, -⟩ := lem_2_3_heights I hg α β hα hβ
  rcases hc with rfl | rfl
  · exact HeightExtend.extend _ _ _ hA hhA h hT
  · exact HeightExtend.extend _ _ _ hB hhB h hT

/-- Proof of Lemma 2.3, v4.24 l. 352-354: "By induction, we get `α = β` outside the component `T` of the forest induced
by `F` that contains `s`" (`T` = the vertices reachable from the sink in `F`). -/
theorem lem_2_3_outside {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    ∀ v, ¬ (I.fGraph α).Reachable I.sink v → α v = β v := by
  exact CaseAPaper.eq_outside hg hα hβ

/-- Proof of Lemma 2.3, v4.24 l. 354-361: for a greedy colouring `c` whose sink colour is not `0` and a height `h`
of `c` on the forest `F`, every vertex `v ≠ s` of the tree `T` (reachable from `s` in `F`) has `h(v) − h(s) ∈ {0, 1}`
if `c(s) = 1`, `∈ {−1, 0}` if `c(s) = 2`, and `∈ {1, 2}` if `c(s) = 3`. -/
theorem lem_2_3_offsets {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (c0 : Fin 4) (c : W → Fin 4)
    (hc : I.IsGreedy c0 c) (hc0 : c0 ≠ 0) (h : W → ℤ) (hh : IsHeight (I.fGraph c) c h) (v : W)
    (hv : (I.fGraph c).Reachable I.sink v) (hvs : v ≠ I.sink) :
    (c0 = 1 → h v - h I.sink = 0 ∨ h v - h I.sink = 1) ∧ (c0 = 2 → h v - h I.sink = -1 ∨ h v - h I.sink = 0) ∧
      (c0 = 3 → h v - h I.sink = 1 ∨ h v - h I.sink = 2) := by
  exact lem_2_3_offsets_proved I c0 c hc hc0 h hh v hv hvs

/-- Proof of Lemma 2.3, v4.24 l. 366-369: with heights as in `lem_2_3_heights`, `E = h_β − h_α` is even and
`|E(v)| ≤ 4` on the tree `T`. -/
theorem lem_2_3_E_bound {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (hA hB : W → ℤ)
    (hhA : IsHeight (I.fGraph α) α hA) (hhB : IsHeight (I.fGraph α) β hB)
    (hs : hB I.sink - hA I.sink = 2 ∨ hB I.sink - hA I.sink = -2) (v : W) (hv : (I.fGraph α).Reachable I.sink v) :
    Even (hB v - hA v) ∧ |hB v - hA v| ≤ 4 := by
  exact lem_2_3_E_bound_proved I hg α β hα hβ hA hB hhA hhB hs v hv

/-- Proof of Lemma 2.3, v4.24 l. 371-375, and Section 3, v4.24 l. 430-431 (the paper's own route): Lemma 2.4 on `T` with
root `s` and `P(s) = L(s) = {g, x}` turns `α` into `β`; every vertex `v` of `T` moves exactly `|E(v)|/2` times, no
other vertex moves, the sink moves exactly once, and there are `½ ∑ |E| ≤ 2m` moves. -/
theorem lem_2_3_paper_route {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (hA hB : W → ℤ)
    (hhA : IsHeight (I.fGraph α) α hA) (hhB : IsHeight (I.fGraph α) β hB)
    (hs : hB I.sink - hA I.sink = 2 ∨ hB I.sink - hA I.sink = -2) :
    ∃ ms, I.IsSeq α ms β ∧
      (∀ v, (I.fGraph α).Reachable I.sink v → 2 * movesOf ms v = (hB v - hA v).natAbs) ∧
      (∀ v, ¬ (I.fGraph α).Reachable I.sink v → movesOf ms v = 0) ∧
      movesOf ms I.sink = 1 ∧ ms.length ≤ 2 * Fintype.card W := by
  exact lem_2_3_paper_route_proved I hg α β hα hβ hA hB hhA hhB hs

/-- Lemma 2.4 (lem:T), v4.24 l. 309-315: tree `T` with root `r`; every other vertex may use `1,2,3`, `r` may use
`P ⊆ {1,2,3}`; `c, c'` proper within these sets, `h` a height of `c`, `E` even with `h + E` a height of `c'`, and
`|E r| ≤ 2` if `|P| ≤ 2`. Then `c` changes into `c'` inside `T` by exactly `½ ∑ |E v|` moves, in which every vertex
`v` moves exactly `|E v|/2` times (intermediate colourings proper and allowed: `def_2_2_seq_proper`). -/
theorem lem_2_4 {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) (hT : T.IsTree) (r : W)
    (P : Finset (Fin 4)) (hP : P ⊆ {1, 2, 3}) (c c' : W → Fin 4) (hc : IsProperFn T c) (hc' : IsProperFn T c')
    (hcA : ∀ v, c v ∈ treeLists r P v) (hc'A : ∀ v, c' v ∈ treeLists r P v)
    (h E : W → ℤ) (hh : IsHeight T c h) (hE : ∀ v, Even (E v)) (hhE : IsHeight T c' (h + E))
    (hr : P.card ≤ 2 → |E r| ≤ 2) :
    ∃ ms, IsSeq T (treeLists r P) c ms c' ∧ 2 * ms.length = ∑ v, (E v).natAbs ∧
      ∀ v, 2 * movesOf ms v = (E v).natAbs := by
  exact lem_2_4_proved T hT r P hP c c' hc hc' hcA hc'A h E hh hE hhE hr

/-- Section 2, v4.24 l. 303-304: "A move changes the current height function by `±2` at the moved vertex only. (In a
`3`-colouring of a tree, a vertex can be recoloured only when all its neighbours have the same colour, and then its
height changes by `±2`.)" Proved for every graph `T` with a height function (a tree is a special case). -/
theorem sec2_tree_move {W : Type} [DecidableEq W] (T : SimpleGraph W) (c : W → Fin 4)
    (hc : ∀ w, c w ∈ ({1, 2, 3} : Finset (Fin 4))) (h : W → ℤ) (hh : IsHeight T c h) (v : W) (y : Fin 4)
    (hm : LegalMove T (fun _ => ({1, 2, 3} : Finset (Fin 4))) c (v, y)) :
    (∀ u w, T.Adj v u → T.Adj v w → c u = c w) ∧
      ∃ h' : W → ℤ, IsHeight T (Function.update c v y) h' ∧ (h' v = h v + 2 ∨ h' v = h v - 2) ∧
        ∀ u, u ≠ v → h' u = h u :=
  sec2_tree_move_proved T c hc h hh v y hm

/-- Lemma 2.4, v4.24 l. 316-317: "The condition on `E(r)` makes `r`, which may have fewer than three allowed colours, move
at most once, and then directly to `c'(r)`" (the hypotheses of `lem_2_4`, with `|P| ≤ 2`). -/
theorem lem_2_4_root_once {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) (hT : T.IsTree) (r : W)
    (P : Finset (Fin 4)) (hP : P ⊆ {1, 2, 3}) (c c' : W → Fin 4) (hc : IsProperFn T c) (hc' : IsProperFn T c')
    (hcA : ∀ v, c v ∈ treeLists r P v) (hc'A : ∀ v, c' v ∈ treeLists r P v)
    (h E : W → ℤ) (hh : IsHeight T c h) (hE : ∀ v, Even (E v)) (hhE : IsHeight T c' (h + E))
    (hr : P.card ≤ 2 → |E r| ≤ 2) (hP2 : P.card ≤ 2) :
    ∃ ms, IsSeq T (treeLists r P) c ms c' ∧ (∀ v, 2 * movesOf ms v = (E v).natAbs) ∧ movesOf ms r ≤ 1 ∧
      ∀ m ∈ ms, m.1 = r → m.2 = c' r :=
  lem_2_4_root_once_proved T hT r P hP c c' hc hc' hcA hc'A h E hh hE hhE hr hP2

/-- Proof of Lemma 2.5, v4.24 l. 391-392: there is exactly one colouring `γ` of `G` in which all vertices are
greedy (each takes the least colour that no out-neighbour has; greedy is defined in Section 2, l. 248-249). -/
theorem sweep_greedy_unique {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (ρ : V ≃ Fin n) (hρ : IsDegOrder G 2 ρ) :
    ∃! γ : V → Fin 4, ∀ v, IsLeastFree univ ((laterNbrs G ρ v).image γ) (γ v) := by
  exact sweep_greedy_unique_proved G ρ hρ

/-- Lemma 2.5 (lem:sweep, the sweep), v4.24 l. 382-389: a class `𝒞` of instances (a predicate on skeletons, so closed
under changing the lists) and `λ ≥ 2` such that every instance of `𝒞` with `g = 0` has a sequence from `α` to
`β` of at most `λ |V(I)|` moves; an order of `G` with at most `2` later neighbours per vertex whose cone instances
all lie in `𝒞`. Then `diam R_4(G) ≤ 2λ (|C_1| + ⋯ + |C_n|) ≤ λ n (n+1)` (with `R_4(G)` connected). -/
theorem lem_2_5 (𝒞 : InstanceClass) (lam : ℝ) (hlam : 2 ≤ lam)
    (hlin : ∀ (W : Type) [Fintype W] [DecidableEq W] (I : Instance W), 𝒞 W I.toSkeleton → I.g = 0 →
      ∀ α β : W → Fin 4, I.IsGreedy I.x α → I.IsGreedy I.g β →
        ∃ ms, I.IsSeq α ms β ∧ (ms.length : ℝ) ≤ lam * Fintype.card W)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (ρ : V ≃ Fin n)
    (hρ : IsDegOrder G 2 ρ) (hcones : ∀ w, 𝒞 (ConeV G ρ w) (coneSkeleton G ρ hρ w)) :
    (recolGraph G 4).ediam ≠ ⊤ ∧
      ((recolGraph G 4).diam : ℝ) ≤ 2 * lam * ∑ w, ((cone G ρ w).card : ℝ) ∧
      2 * lam * ∑ w, ((cone G ρ w).card : ℝ) ≤ lam * n * (n + 1) := by
  exact lem_2_5_proved 𝒞 lam hlam hlin G ρ hρ hcones

/-- Section 2, v4.24 l. 286-287 (the proof of Theorem 1.2 uses it, l. 584-585: "the instance on it is single-sink"): in
the instance on a cone `C_t`, "`v_t` has none, and every other vertex of `C_t` has one in `C_t`, the next vertex on a
directed path of arcs to `v_t`. So the instance on `C_t` is single-sink" (none, one: out-neighbours); so the instances
of the sweep are single-sink (`NoRoots`). -/
theorem thm_1_2_cone_out_neighbour {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (ρ : V ≃ Fin n) (hρ : IsDegOrder G 2 ρ) (w : V) : (coneSkeleton G ρ hρ w).NoRoots := by
  exact thm_1_2_cone_out_neighbour_proved G ρ hρ w

/-! ## Section 3 — Bipartite graphs: proof of Theorem 1.2 -/

/-- Section 3, v4.24 l. 430-431 ("Lemma 2.3 gives a sequence as in Theorem 3.1"), along the paper's own proof of Lemma 2.3. Take
the heights of `lem_2_3_heights` and the sequence of `lem_2_3_paper_route`: a vertex of `T` moves
`|E(v)|/2 ≤ 2` times (`lem_2_3_E_bound`), a vertex outside `T` does not move, and the sink moves exactly once. -/
theorem sec3_caseA_counts {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    ∃ ms, I.IsSeq α ms β ∧ movesOf ms I.sink = 1 ∧ ∀ v, v ≠ I.sink → movesOf ms v ≤ 2 := by
  obtain ⟨hA, hB, hhA, hhB, hs⟩ := lem_2_3_heights I hg α β hα hβ
  obtain ⟨ms, hseq, hmv, hout, hsink, -⟩ := lem_2_3_paper_route I hg α β hα hβ hA hB hhA hhB hs
  refine ⟨ms, hseq, hsink, fun v _ => ?_⟩
  by_cases hv : (I.fGraph α).Reachable I.sink v
  · have h2 := hmv v hv
    have h4 : |hB v - hA v| ≤ 4 := (lem_2_3_E_bound I hg α β hα hβ hA hB hhA hhB hs v hv).2
    have h4' : (hB v - hA v).natAbs ≤ 4 := by
      rw [Int.abs_eq_natAbs] at h4
      exact_mod_cast h4
    omega
  · rw [hout v hv]
    omega

/-- Lemma 2.3 (lem:caseA), v4.24 l. 292-295, the whole statement: in an instance with `m` vertices whose sink has the
list `{g, x}` with `0 < g < x` there is a sequence from `α` to `β` of length at most `2m` in which the sink moves
exactly once and every other vertex at most twice. Along the paper's proof (`sec3_caseA_counts`). -/
theorem lem_2_3_full {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    ∃ ms, I.IsSeq α ms β ∧ ms.length ≤ 2 * Fintype.card W ∧ movesOf ms I.sink = 1 ∧
      ∀ v, v ≠ I.sink → movesOf ms v ≤ 2 := by
  obtain ⟨ms, hseq, h1, h2⟩ := sec3_caseA_counts I hg α β hα hβ
  have hlen := Bip.length_le_of_counts I ms h1 h2
  exact ⟨ms, hseq, by omega, h1, h2⟩

/-- Theorem 3.1 (thm:BIPinst), v4.24 l. 424-427: in a bipartite single-sink instance with `m` vertices there is a
sequence from `α` to `β` in which the sink moves exactly once and every other vertex at most twice; its length is at
most `2m − 1`. Along the paper's proof: the case `g ≠ 0` by Lemma 2.3 (l. 430-431, `sec3_caseA_counts`), the case `g = 0`
by Lemma 3.4 with the greedy `μ` of Definition 3.7 and Proposition 3.8 (l. 479, 503 and 562-564). Theorem 1.2
(`thm_1_2`) uses it. -/
theorem thm_3_1 {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots)
    (hbip : I.graph.IsBipartite) (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    ∃ ms, I.IsSeq α ms β ∧ movesOf ms I.sink = 1 ∧ (∀ v, v ≠ I.sink → movesOf ms v ≤ 2) ∧
      ms.length ≤ 2 * Fintype.card W - 1 := by
  exact thm_3_1_of_v40 (fun I hg α β hα hβ => sec3_caseA_counts I hg α β hα hβ) I hnr hbip α β hα hβ

/-- Section 3, v4.24 l. 429-430: a vertex with two out-neighbours has the list `{0,1,2,3}`. -/
theorem sec3_two_out_full_list {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (v : W)
    (hv : (I.out v).card = 2) : I.L v = univ := by
  exact sec3_two_out_full_list_proved I v hv

/-- Lemma 3.2 (lem:s1), v4.24 l. 435-436: for every vertex `v ≠ s`, `α(v), β(v) ∈ {0,1,2}` (no hypothesis on the
instance is needed). -/
theorem lem_3_2 {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (v : W) (hv : v ≠ I.sink) : α v ≤ 2 ∧ β v ≤ 2 := by
  exact lem_3_2_proved I α β hα hβ v hv

/-- Section 3, v4.24 l. 443-446: "the pattern of the sink is `(x, 0)`", and "the sink is a joiner" (with `g = 0`). -/
theorem sec3_sink_joiner {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg0 : I.g = 0)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) : IsJoiner α β I.sink :=
  (sec3_kinds_proved I hg0 α β hα hβ).2.2.2.2

/-- Lemma 3.3 (lem:s3), v4.24 l. 450-451: every leaver has an out-neighbour that is a joiner, and every joiner other
than `s` has an out-neighbour that is a leaver. The paper says "In an instance with `g = 0`"; Lean needs no hypothesis
on the instance, so this is stronger. -/
theorem lem_3_3 {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    (∀ v, IsLeaver α β v → ∃ u ∈ I.out v, IsJoiner α β u) ∧
    (∀ v, v ≠ I.sink → IsJoiner α β v → ∃ u ∈ I.out v, IsLeaver α β u) := by
  exact lem_3_3_proved I α β hα hβ

/-- Lemma 3.4 (lem:um), v4.24 l. 459-464: `μ` proper, `μ v ∈ L v`, `μ ≥ α`, `μ ≥ β`, `μ(s) = x`. Recolour first every
vertex from `α(v)` to `μ(v)` in decreasing order of `μ` (`ord1`), then from `μ(v)` to `β(v)` in increasing order of
`μ` (`ord2`); ties in any order, no move when the colours agree. This is a sequence from `α` to `β` in which every
vertex moves at most twice and the sink once. -/
theorem lem_3_4 {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (α β μ : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (hμ : IsProperFn I.graph μ) (hμL : ∀ v, μ v ∈ I.L v)
    (hμα : ∀ v, α v ≤ μ v) (hμβ : ∀ v, β v ≤ μ v) (hμs : μ I.sink = I.x)
    (ord1 ord2 : List W) (h1 : ord1.Nodup ∧ ∀ v, v ∈ ord1) (h2 : ord2.Nodup ∧ ∀ v, v ∈ ord2)
    (hs1 : ord1.Pairwise (fun u v => μ v ≤ μ u)) (hs2 : ord2.Pairwise (fun u v => μ u ≤ μ v)) :
    I.IsSeq α ((ord1.filter (fun v => α v ≠ μ v)).map (fun v => (v, μ v)) ++
        (ord2.filter (fun v => μ v ≠ β v)).map (fun v => (v, β v))) β ∧
      (∀ v, movesOf ((ord1.filter (fun v => α v ≠ μ v)).map (fun v => (v, μ v)) ++
        (ord2.filter (fun v => μ v ≠ β v)).map (fun v => (v, β v))) v ≤ 2) ∧
      movesOf ((ord1.filter (fun v => α v ≠ μ v)).map (fun v => (v, μ v)) ++
        (ord2.filter (fun v => μ v ≠ β v)).map (fun v => (v, β v))) I.sink = 1 := by
  exact lem_3_4_proved I α β μ hα hβ hμ hμL hμα hμβ hμs ord1 ord2 h1 h2 hs1 hs2

/-- Section 3, v4.24 l. 474-477 (the example after Lemma 3.4; the instance `ex2`, Defs/Example2.lean): "Then `α(u) = 0`
and `β(u) = 1`. We can take `μ(u) = 2`. Neither `s` nor `u` can move directly to its colour in `β`, the current colour
of the other. So `u` first rises to `2`, then `s` moves to `0`, and `u` moves down to `1`." (`μ = (s ↦ 1, u ↦ 2)`
satisfies the hypotheses of Lemma 3.4, `lem_3_4`.) -/
theorem sec3_example_two :
    (∃ α, ex2.IsGreedy ex2.x α) ∧ (∃ β, ex2.IsGreedy ex2.g β) ∧
    ∀ α β : Fin 2 → Fin 4, ex2.IsGreedy ex2.x α → ex2.IsGreedy ex2.g β →
      α 1 = 0 ∧ β 1 = 1 ∧
      (IsProperFn ex2.graph (![1, 2] : Fin 2 → Fin 4) ∧ (∀ v, (![1, 2] : Fin 2 → Fin 4) v ∈ ex2.L v) ∧
        (∀ v, α v ≤ (![1, 2] : Fin 2 → Fin 4) v ∧ β v ≤ (![1, 2] : Fin 2 → Fin 4) v) ∧
        (![1, 2] : Fin 2 → Fin 4) ex2.sink = ex2.x) ∧
      ¬ LegalMove ex2.graph ex2.L α (0, β 0) ∧ ¬ LegalMove ex2.graph ex2.L α (1, β 1) ∧
      ex2.IsSeq α [(1, 2), (0, 0), (1, 1)] β :=
  sec3_example_two_proved

/-- Section 3, v4.24 l. 503-505: "We shall choose `μ` greedily, in instance order (Definition 3.7). A count of colours
shows that this can fail only at a vertex on `2` in `α` or in `β` whose two out-neighbours take both `2` and `3` in
`μ`." Proved without bipartiteness and for any colours `μ` of the out-neighbours: if no colour of `L(v)` at least
`max(α(v), β(v))` avoids them, then `v` is on `2` in `α` or `β` and two out-neighbours take `2` and `3`. -/
theorem sec3_mu_count {W : Type} [Fintype W] [DecidableEq W] (I : Instance W)
    (α β μ : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (v : W) (hv : v ≠ I.sink)
    (hfail : ¬ ∃ y ∈ I.L v, max (α v) (β v) ≤ y ∧ ∀ u ∈ I.out v, μ u ≠ y) :
    (α v = 2 ∨ β v = 2) ∧ ∃ u ∈ I.out v, ∃ w ∈ I.out v, μ u = 2 ∧ μ w = 3 :=
  sec3_mu_count_proved I α β μ hα hβ v hv hfail

/-- Section 3, v4.24 l. 480: a single-sink instance (`NoRoots`) "is connected, since every vertex reaches `s` through
out-neighbours". -/
theorem sec3_connected {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots) :
    I.graph.Connected := by
  exact sec3_connected_proved I hnr

/-- Lemma 3.5 (lem:sides), v4.24 l. 484-487 (bipartite single-sink instance with `g = 0`; `side` is any proper
2-colouring of the instance graph and `S_0` is the side of `s`): a vertex of `S_0 \ {s}` has one of the patterns
`(0,0),(1,1),(2,2),(1,0),(2,0),(1,2)`, a vertex of `S_1` one of `(0,0),(1,1),(2,2),(0,1),(0,2),(2,1)`. -/
theorem lem_3_5 {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots) (hg0 : I.g = 0)
    (side : W → Fin 2) (hside : IsProperFn I.graph side) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (v : W) :
    (v ≠ I.sink → side v = side I.sink →
      (α v, β v) ∈ ({(0, 0), (1, 1), (2, 2), (1, 0), (2, 0), (1, 2)} : Finset (Fin 4 × Fin 4))) ∧
    (side v ≠ side I.sink →
      (α v, β v) ∈ ({(0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (2, 1)} : Finset (Fin 4 × Fin 4))) := by
  exact lem_3_5_proved I hnr hg0 side hside α β hα hβ v

/-- Proof of Lemma 3.5, v4.24 l. 491-495 ("We show that a leaver lies in `S_1`, a joiner other than `s` lies in `S_0`,
a vertex with the pattern `(2,1)` lies in `S_1`, and a vertex with the pattern `(1,2)` lies in `S_0`"): every joiner
lies on the side of `s` and every leaver on the other side; a vertex `v ≠ s` that is not fixed and is on `0` neither
in `α` nor in `β` has the pattern `(1,2)` on `S_0` and `(2,1)` on `S_1` (from the pattern lists of l. 485-487). -/
theorem lem_3_5_equiv {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots) (hg0 : I.g = 0)
    (side : W → Fin 2) (hside : IsProperFn I.graph side) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    (∀ v, IsJoiner α β v → side v = side I.sink) ∧ (∀ v, IsLeaver α β v → side v ≠ side I.sink) ∧
    (∀ v, v ≠ I.sink → ¬ IsFixed α β v → α v ≠ 0 → β v ≠ 0 →
      (side v = side I.sink → α v = 1 ∧ β v = 2) ∧ (side v ≠ side I.sink → α v = 2 ∧ β v = 1)) := by
  exact lem_3_5_equiv_proved I hnr hg0 side hside α β hα hβ

/-! ### Section 3, v4.24 l. 508-565: Lemma 3.6, the colouring `μ` of Definition 3.7 (`IsGreedyMu`), Proposition 3.8
and the proof of Theorem 3.1 -/

/-- Lemma 3.6 (lem:twofacts), v4.24 l. 508-513 (bipartite single-sink instance with `g = 0`): (a) every
out-neighbour of a vertex fixed on `2` is fixed on `0` or on `1`; (b) every vertex with two out-neighbours that is not
fixed and has the colour `2` in `α` or in `β` has an out-neighbour fixed on `0` or on `1`. -/
theorem lem_3_6 {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots)
    (hbip : I.graph.IsBipartite) (hg0 : I.g = 0) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    (∀ v, IsFixed α β v → α v = 2 → ∀ p ∈ I.out v, IsFixed α β p ∧ (α p = 0 ∨ α p = 1)) ∧
    (∀ v, (I.out v).card = 2 → ¬ IsFixed α β v → (α v = 2 ∨ β v = 2) →
      ∃ p ∈ I.out v, IsFixed α β p ∧ (α p = 0 ∨ α p = 1)) := by
  exact lem_3_6_v40_proved I hnr hbip hg0 α β hα hβ

/-- Proposition 3.8 (prop:mu), v4.24 l. 535-537 (bipartite single-sink instance with `g = 0`): `μ`
(Definition 3.7) is well defined (it exists, and it is unique), and `μ(v) = α(v)` for every fixed vertex `v`. -/
theorem prop_3_8 {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots)
    (hbip : I.graph.IsBipartite) (hg0 : I.g = 0) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    (∃! μ, IsGreedyMu I α β μ) ∧ ∀ μ, IsGreedyMu I α β μ → ∀ v, IsFixed α β v → μ v = α v := by
  exact prop_3_8_v40_proved I hnr hbip hg0 α β hα hβ

/-- Proof of Theorem 3.1, v4.24 l. 562-564: the greedy `μ` is proper, within the lists, at least `α` and
`β`, and `μ(s) = x` (the hypotheses of Lemma 3.4). -/
theorem thm_3_1_mu_greedy {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots)
    (hbip : I.graph.IsBipartite) (hg0 : I.g = 0) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (μ : W → Fin 4) (hμ : IsGreedyMu I α β μ) :
    IsProperFn I.graph μ ∧ (∀ v, μ v ∈ I.L v) ∧ (∀ v, α v ≤ μ v ∧ β v ≤ μ v) ∧ μ I.sink = I.x := by
  exact thm_3_1_mu_v40_proved I hnr hbip hg0 α β hα hβ μ hμ

/-- **Remark 3.9** (rem:triangle), v4.24 l. 567-579: without bipartiteness a colouring `μ` as in Lemma 3.4 (lem:um)
need not exist. The instance `tri` (sink `s` with the list `{0,1}` and `x = 1`; `N⁺(u₁) = {s}`, `N⁺(u₂) = {u₁}`,
`N⁺(u₃) = {u₁, u₂}`; `L(u₁) = L(u₃) = {0,1,2,3}`, `L(u₂) = {1,2,3}`; `u_i` = `i`, `s` = `0`) is single-sink with `g = 0`;
its edges are the triangle `u₁ u₂ u₃` and the edge `s u₁` (so it is not bipartite); the patterns of `u₁, u₂, u₃` are
`(0,1)`, `(1,2)`, `(2,0)`; a colouring with `μ ≥ α`, `μ ≥ β`, `μ(s) = x` and `μ(u₁) ≠ μ(s)` has `μ(u₁) ≥ 1`,
`μ(u₁) ≠ 1` and `μ(u₂), μ(u₃) ≥ 2`, so it uses only `2` and `3` on the triangle; hence no `μ` as in Lemma 3.4 exists;
"The conclusion of Lemma 3.6(b) fails at `u₃`, which has two out-neighbours, is not fixed and is on `2` in `α`, while
neither of its out-neighbours is fixed" (l. 574-576; lem:twofacts, `lem_3_6`); and the five moves `triMoves` are a sequence from `α` to `β` of length `5` as in Theorem 3.1 (thm:BIPinst: the sink moves exactly
once, every other vertex at most twice). -/
theorem rem_3_9 :
    tri.IsSingleSink ∧ tri.g = 0 ∧
    (∀ u v, tri.graph.Adj u v ↔ s(u, v) ∈ ({s(1, 2), s(2, 3), s(1, 3), s(0, 1)} : Finset (Sym2 (Fin 4)))) ∧
    ¬ tri.graph.IsBipartite ∧
    ∀ α β : Fin 4 → Fin 4, tri.IsGreedy tri.x α → tri.IsGreedy tri.g β →
      ((α 1, β 1) = (0, 1) ∧ (α 2, β 2) = (1, 2) ∧ (α 3, β 3) = (2, 0)) ∧
      (∀ μ : Fin 4 → Fin 4, (∀ v, α v ≤ μ v) → (∀ v, β v ≤ μ v) → μ tri.sink = tri.x → μ 1 ≠ μ tri.sink →
        1 ≤ μ 1 ∧ μ 1 ≠ 1 ∧ 2 ≤ μ 2 ∧ 2 ≤ μ 3 ∧
          μ 1 ∈ ({2, 3} : Finset (Fin 4)) ∧ μ 2 ∈ ({2, 3} : Finset (Fin 4)) ∧ μ 3 ∈ ({2, 3} : Finset (Fin 4))) ∧
      (¬ ∃ μ : Fin 4 → Fin 4, IsProperFn tri.graph μ ∧ (∀ v, μ v ∈ tri.L v) ∧ (∀ v, α v ≤ μ v) ∧
        (∀ v, β v ≤ μ v) ∧ μ tri.sink = tri.x) ∧
      ((tri.out 3).card = 2 ∧ ¬ IsFixed α β 3 ∧ α 3 = 2 ∧ (∀ u ∈ tri.out 3, ¬ IsFixed α β u) ∧
        ¬ ∃ p ∈ tri.out 3, IsFixed α β p ∧ (α p = 0 ∨ α p = 1)) ∧
      (tri.IsSeq α triMoves β ∧ triMoves.length = 5 ∧ movesOf triMoves tri.sink = 1 ∧
        ∀ v, v ≠ tri.sink → movesOf triMoves v ≤ 2) :=
  rem_3_9_proved

/-- Proof of Theorem 1.2, v4.24 l. 584-585: "the cone induces a bipartite subgraph of `G`", and the cone instance is
single-sink (`NoRoots`). -/
theorem thm_1_2_cones {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) {n : ℕ} (ρ : V ≃ Fin n) (hρ : IsDegOrder G 2 ρ) (w : V) :
    (coneSkeleton G ρ hρ w).graph.IsBipartite ∧ (coneSkeleton G ρ hρ w).NoRoots := by
  exact thm_1_2_cones_proved G hbip ρ hρ w

/-- Theorem 1.2 assembled from the statements of Sections 2-3 (not a separate claim: `thm_1_2` below restates it;
Section 4 uses it for the connectivity of `R_4(H_n)` and `R_4(J_n)`). -/
private theorem thm_1_2_early {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) (hdeg : IsDegenerate G 2) :
    (recolGraph G 4).ediam ≤ ((2 * Fintype.card V * (Fintype.card V + 1) : ℕ) : ℕ∞) := by
  refine thm_1_2_of ?_ ?_ ?_ ?_ G hbip hdeg
  · intro V _ _ G _ d; exact sec2_order_iff_degenerate_proved G d
  · intro 𝒞 lam hlam hlin V _ _ G _ n ρ hρ hc; exact lem_2_5 𝒞 lam hlam hlin G ρ hρ hc
  · intro W _ _ I hnr hbip α β hα hβ; exact thm_3_1 I hnr hbip α β hα hβ
  · intro V _ _ G _ hbip n ρ hρ w; exact thm_1_2_cones G hbip ρ hρ w

/-! ## Section 4 — Lower bounds: proof of Proposition 1.3

Naming (v4.24 l. 590-591): "`ℓ` is the number of vertices of a path and `n` that of the whole graph" (`H_ℓ` has `n = ℓ + 2`, `J_ℓ` has `n = ℓ + 4` vertices). In this section Lean's `n` is the paper's
`ℓ`, and the docstrings below that say "`N` vertices" or "`(N − 7)²/8`" mean the paper's `n`. -/

/-- Section 4.1, v4.24 l. 625-628: `H_n` has `N = n + 2` vertices; it is bipartite with sides
(odd path vertices and `b`; even path vertices and `a`), planar, and `2`-degenerate (in the order
`v_1, …, v_n, a, b` every vertex has at most two later neighbours). -/
theorem sec4_Hgraph (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (Fin n ⊕ Fin 2) = n + 2 ∧
      IsProperFn (Hgraph n) (sideH n) ∧ IsStraightLinePlanar (Hgraph n) ∧
      IsDegOrder (Hgraph n) 2 (finSumFinEquiv : Fin n ⊕ Fin 2 ≃ Fin (n + 2)) := by
  exact sec4_Hgraph_proved n hn

/-- Section 4.1, v4.24 l. 628-629 ("For `ℓ ≥ 3` it contains the `4`-cycle `a v_1 v_2 v_3 a`, so it is not a forest, and
its degeneracy is `2`"; Proposition 1.3, "degeneracy `2`", l. 84-89): `H_n` (`n ≥ 3`) is not `1`-degenerate. -/
theorem sec4_Hgraph_not_one_degenerate (n : ℕ) (hn : 3 ≤ n) : ¬ IsDegenerate (Hgraph n) 1 := by
  exact sec4_Hgraph_not_one_degenerate_proved n hn

/-- Section 4.1, v4.24 l. 628-629: "For `ℓ ≥ 3` it contains the `4`-cycle `a v_1 v_2 v_3 a`, so it is not a forest".
Lean: the closed walk `a, v_1, v_2, v_3, a` (`a = Sum.inr 0`, `v_i = Sum.inl (i-1)`) is a cycle of length `4`, so
`H_n` (`n ≥ 3`) is not acyclic. -/
theorem sec4_Hgraph_four_cycle (n : ℕ) (hn : 3 ≤ n) :
    ∃ w : (Hgraph n).Walk (.inr 0) (.inr 0), w.IsCycle ∧ w.length = 4 ∧
      w.support = [.inr 0, .inl ⟨0, by omega⟩, .inl ⟨1, by omega⟩, .inl ⟨2, by omega⟩, .inr 0] ∧
      ¬ (Hgraph n).IsAcyclic := by
  exact sec4_Hgraph_four_cycle_proved n hn

/-- Proposition 4.1 (prop:LBH), v4.24 l. 631-635: for `n ≥ 5` the proper `4`-colourings `σ⁺, σ⁻` of `H_n` are at
distance at least `(n-5)²/8` in `R_4(H_n)` (every walk between them is that long); hence
`diam R_4(H_n) ≥ (N-7)²/8`. -/
theorem prop_4_1 (n : ℕ) (hn : 5 ≤ n) :
    (∃ σp σm : (Hgraph n).Coloring (Fin 4), ⇑σp = sigmaPlus n 2 ∧ ⇑σm = sigmaMinus n 2 ∧
      ∀ p : (recolGraph (Hgraph n) 4).Walk σp σm, ((n : ℝ) - 5) ^ 2 / 8 ≤ p.length) ∧
    ((((n + 2 : ℕ) : ℝ) - 7) ^ 2 / 8 ≤ ((recolGraph (Hgraph n) 4).diam : ℝ)) := by
  exact prop_4_1_proved n hn (Sec4Aux.hfinH @thm_1_2_early n)

/-- Proposition 4.1 (prop:LBH), v4.24 l. 626 and 632-634: `H_ℓ` "has `n = ℓ + 2` vertices", and for `ℓ ≥ 5`, "Hence
`diam R_4(H_ℓ) ≥ (n−7)²/8`". The paper's `ℓ` is Lean's `l` (the `n` of `prop_4_1`); the paper's `n` is
`Fintype.card` of the vertex type. -/
theorem prop_4_1_vertices (l : ℕ) (hl : 5 ≤ l) :
    Fintype.card (Fin l ⊕ Fin 2) = l + 2 ∧
    (((Fintype.card (Fin l ⊕ Fin 2) : ℕ) : ℝ) - 7) ^ 2 / 8 ≤ ((recolGraph (Hgraph l) 4).diam : ℝ) :=
  prop_4_1_vertices_proved l hl (Sec4Aux.hfinH @thm_1_2_early l)

/-- Section 4, v4.24 l. 637-642: in a plain proper colouring (of any path-with-apices graph) the steps are defined,
so a height function exists; for `σ⁺` all steps are `+1` and for `σ⁻` all are `-1`. -/
theorem sec4_path_height (n k : ℕ) (f : Fin n → Fin k) :
    (∀ c : Fin n ⊕ Fin k → Fin 4, IsProperFn (pathApex n k f) c → IsPlain c → ∃ h, IsPathHeight c h) ∧
    IsPathHeight (sigmaPlus n k) (fun i => (i : ℤ)) ∧ IsPathHeight (sigmaMinus n k) (fun i => -(i : ℤ)) := by
  exact sec4_path_height_proved n k f

/-- Section 4, v4.24 l. 641: "We define the winding of `c` as `W = h(ℓ) − h(1)`. It does not depend on the choice of
`h`":
two height functions of the same plain colouring differ by a constant on the path. -/
theorem sec4_winding_well_defined {n k : ℕ} (c : Fin n ⊕ Fin k → Fin 4) (h h' : ℕ → ℤ) (hh : IsPathHeight c h)
    (hh' : IsPathHeight c h') (i j : ℕ) (hi : i < n) (hj : j < n) : h i - h j = h' i - h' j :=
  sec4_winding_well_defined_proved c h h' hh hh' i j hi hj

/-- Lemma 4.2 (lem:h1), v4.24 l. 644-647, for every path-with-apices graph (so for `H_n` and, as the paper says
after Proposition 4.6, l. 734-735, for `J_n`): a move of a path vertex between two plain colourings changes one value
of a height function by exactly `2` and keeps the others. -/
theorem lem_4_2 (n k : ℕ) (f : Fin n → Fin k) (c c' : Fin n ⊕ Fin k → Fin 4)
    (hc : IsProperFn (pathApex n k f) c) (hpc : IsPlain c) (hpc' : IsPlain c') (i : Fin n)
    (hmove : LegalMove (pathApex n k f) (fun _ => univ) c (.inl i, c' (.inl i)))
    (hrest : ∀ w, w ≠ .inl i → c' w = c w) (h : ℕ → ℤ) (hh : IsPathHeight c h) :
    ∃ ε : ℤ, (ε = 2 ∨ ε = -2) ∧ IsPathHeight c' (Function.update h i.val (h i.val + ε)) := by
  exact lem_4_2_proved n k f c c' hc hpc hpc' i hmove hrest h hh

/-- Lemma 4.3 (lem:flat), v4.24 l. 657-658: if a plain colouring of `H_n` allows a move of `a` or of `b`, then
`|W| ≤ 4` (`W = h(n) - h(1)`, here `h (n-1) - h 0`). -/
theorem lem_4_3 (n : ℕ) (c : Fin n ⊕ Fin 2 → Fin 4) (hc : IsProperFn (Hgraph n) c) (hp : IsPlain c)
    (hmove : ∃ j y, LegalMove (Hgraph n) (fun _ => univ) c (.inr j, y)) (h : ℕ → ℤ)
    (hh : IsPathHeight c h) : |h (n - 1) - h 0| ≤ 4 := by
  exact lem_4_3_proved n c hc hp hmove h hh

/-- Lemma 4.4 (lem:cost), v4.24 l. 676-678: `h, h'` on `{1..n}` with all steps `±1`, all steps of `h` equal to `+1`,
`q ≥ 0`, `h'(n) - h'(1) ≤ (n-1) - q`, `q/4 + 1 ≤ n/2`. Then `∑ |h'(i) - h(i)| ≥ q²/8` (0-based indices). -/
theorem lem_4_4 (n : ℕ) (h h' : ℕ → ℤ) (q : ℝ)
    (hh : ∀ i, i + 1 < n → h (i + 1) - h i = 1)
    (hh' : ∀ i, i + 1 < n → h' (i + 1) - h' i = 1 ∨ h' (i + 1) - h' i = -1)
    (hq : 0 ≤ q) (hq' : ((h' (n - 1) - h' 0 : ℤ) : ℝ) ≤ ((n : ℝ) - 1) - q)
    (hqn : q / 4 + 1 ≤ (n : ℝ) / 2) :
    q ^ 2 / 8 ≤ ∑ i ∈ Finset.range n, ((|h' i - h i| : ℤ) : ℝ) :=
  cost_proved n h h' q hh hh' hq hq' hqn

/-- Lemma 4.4, the form with all signs reversed (v4.24 l. 678-679). -/
theorem lem_4_4_mirror (n : ℕ) (h h' : ℕ → ℤ) (q : ℝ)
    (hh : ∀ i, i + 1 < n → h (i + 1) - h i = -1)
    (hh' : ∀ i, i + 1 < n → h' (i + 1) - h' i = 1 ∨ h' (i + 1) - h' i = -1)
    (hq : 0 ≤ q) (hq' : -((n : ℝ) - 1) + q ≤ ((h' (n - 1) - h' 0 : ℤ) : ℝ))
    (hqn : q / 4 + 1 ≤ (n : ℝ) / 2) :
    q ^ 2 / 8 ≤ ∑ i ∈ Finset.range n, ((|h' i - h i| : ℤ) : ℝ) :=
  cost_mirror_proved n h h' q hh hh' hq hq' hqn

/-- Remark 4.5, v4.24 l. 708: `H_n` is the fan (the path `v_1 ⋯ v_n` and one apex joined to every
`v_i`, `pathApex n 1`, as in `intro_fans`) with its apex split into `a` and `b`: `a` and `b` are not adjacent, and
merging them into one apex sends the edges of `H_n` exactly onto the edges of the fan. -/
theorem rem_4_5_apex_split (n : ℕ) :
    ¬ (Hgraph n).Adj (Sum.inr 0) (Sum.inr 1) ∧
    ∀ u v : Fin n ⊕ Fin 1, (pathApex n 1 (fun _ => 0)).Adj u v ↔
      ∃ u' v' : Fin n ⊕ Fin 2, (Hgraph n).Adj u' v' ∧
        Sum.map id (fun _ => (0 : Fin 1)) u' = u ∧ Sum.map id (fun _ => (0 : Fin 1)) v' = v := by
  refine ⟨fun h => h, fun u v => ⟨fun h => ?_, ?_⟩⟩
  · rcases u with i | i <;> rcases v with j | j
    · exact ⟨.inl i, .inl j, h, rfl, rfl⟩
    · exact ⟨.inl i, .inr ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩, rfl, rfl,
        congrArg Sum.inr (Subsingleton.elim _ _)⟩
    · exact ⟨.inr ⟨j.val % 2, Nat.mod_lt _ (by norm_num)⟩, .inl j, rfl,
        congrArg Sum.inr (Subsingleton.elim _ _), rfl⟩
    · exact h.elim
  · rintro ⟨u', v', h, rfl, rfl⟩
    rcases u' with i | i <;> rcases v' with j | j
    · exact h
    · exact rfl
    · exact rfl
    · exact h.elim

/-- Remark 4.5, v4.24 l. 712-713: "The apex of the fan can move only when the path uses at most two colours, whereas `a`
and `b` can move when the path still uses three" (the fan is `pathApex n 1`; for `H_ℓ`, `ℓ ≥ 3`: a plain colouring whose
path uses three colours, in which both `a` and `b` can move). -/
theorem rem_4_5_fan_apex :
    (∀ n (c : Fin n ⊕ Fin 1 → Fin 4), IsProperFn (pathApex n 1 (fun _ => 0)) c →
      (∃ y, LegalMove (pathApex n 1 (fun _ => 0)) (fun _ => Finset.univ) c (.inr 0, y)) →
      (Finset.univ.image (fun i : Fin n => c (.inl i))).card ≤ 2) ∧
    ∀ n, 3 ≤ n → ∃ c : Fin n ⊕ Fin 2 → Fin 4, IsProperFn (Hgraph n) c ∧ IsPlain c ∧
      (Finset.univ.image (fun i : Fin n => c (.inl i))).card = 3 ∧
      (∃ y, LegalMove (Hgraph n) (fun _ => Finset.univ) c (.inr 0, y)) ∧
      (∃ y, LegalMove (Hgraph n) (fun _ => Finset.univ) c (.inr 1, y)) :=
  rem_4_5_fan_apex_proved

/-- Section 1, v4.24 l. 190-191: "An additional vertex can leave the colour `3` only if its path neighbours miss one of
the other three colours" (for every graph `pathApex n k f`, so for `H_ℓ` and `J_ℓ`). -/
theorem intro_apex_leave3 (n k : ℕ) (f : Fin n → Fin k) (c : Fin n ⊕ Fin k → Fin 4) (j : Fin k) (y : Fin 4)
    (h3 : c (.inr j) = 3) (hm : LegalMove (pathApex n k f) (fun _ => Finset.univ) c (.inr j, y)) :
    ∃ z : Fin 4, z ≠ 3 ∧ ∀ i, f i = j → c (.inl i) ≠ z :=
  intro_apex_leave3_proved n k f c j y h3 hm

/-- Section 1, v4.24 l. 194: "So order `ℓ²` moves precede the first move of an additional vertex, and as many follow the
last one." For `H_ℓ` (`ℓ ≥ 5`) and `J_ℓ` (`ℓ ≥ 29`): on a walk from `σ⁺` to `σ⁻`, every move of an additional vertex
has at least `(ℓ-5)²/16`, resp. `(ℓ-29)²/256`, moves before it and after it (the proofs of Propositions 4.1 and 4.6,
l. 697-704 and 755-757). -/
theorem intro_lb_halves :
    (∀ n : ℕ, 5 ≤ n → ∀ σp σm : (Hgraph n).Coloring (Fin 4), ⇑σp = sigmaPlus n 2 → ⇑σm = sigmaMinus n 2 →
      ∀ p : (recolGraph (Hgraph n) 4).Walk σp σm, ∀ i < p.length,
        (∃ j, (p.getVert i) (.inr j) ≠ (p.getVert (i + 1)) (.inr j)) →
        ((n : ℝ) - 5) ^ 2 / 16 ≤ (i : ℝ) ∧ ((n : ℝ) - 5) ^ 2 / 16 ≤ ((p.length - (i + 1) : ℕ) : ℝ)) ∧
    (∀ n : ℕ, 29 ≤ n → ∀ σp σm : (Jgraph n).Coloring (Fin 4), ⇑σp = sigmaPlus n 4 → ⇑σm = sigmaMinus n 4 →
      ∀ p : (recolGraph (Jgraph n) 4).Walk σp σm, ∀ i < p.length,
        (∃ j, (p.getVert i) (.inr j) ≠ (p.getVert (i + 1)) (.inr j)) →
        ((n : ℝ) - 29) ^ 2 / 256 ≤ (i : ℝ) ∧ ((n : ℝ) - 29) ^ 2 / 256 ≤ ((p.length - (i + 1) : ℕ) : ℝ)) :=
  intro_lb_halves_proved

/-- Proof of Proposition 4.1, v4.24 l. 693-696: "If `a` and `b` never move, ... Hence at least `(ℓ-2)²/4 > (ℓ-5)²/8`
moves are needed": Lean proves at least `(ℓ²-1)/4` moves and `(ℓ-2)²/4 ≤ (ℓ²-1)/4` (the paper gets its bound from
Lemma 4.4 with `q = 2ℓ - 4`; Lean counts the full reversal of the height, AUDIT_NOTES.md section 4). -/
theorem prop_4_1_no_move (n : ℕ) (hn : 5 ≤ n) (σp σm : (Hgraph n).Coloring (Fin 4))
    (hσp : ⇑σp = sigmaPlus n 2) (hσm : ⇑σm = sigmaMinus n 2) (p : (recolGraph (Hgraph n) 4).Walk σp σm)
    (hno : ∀ i < p.length, ∀ j, (p.getVert i) (.inr j) = (p.getVert (i + 1)) (.inr j)) :
    ((n : ℝ) - 2) ^ 2 / 4 ≤ ((n : ℝ) ^ 2 - 1) / 4 ∧ ((n : ℝ) ^ 2 - 1) / 4 ≤ p.length ∧
      ((n : ℝ) - 5) ^ 2 / 8 < ((n : ℝ) - 2) ^ 2 / 4 :=
  prop_4_1_no_move_proved n hn σp σm hσp hσm p hno

/-- Remark 4.5, v4.24 l. 712-713: "whereas `a` and `b` can move when the path still uses three" (colours): for `ℓ ≥ 3`
there is a plain proper colouring of `H_ℓ` whose path uses the colours `0, 1, 2` and in which an apex can be
recoloured (some colour `y ≠ 3` is used by none of its neighbours). -/
theorem rem_4_5_three_colours_move (n : ℕ) (hn : 3 ≤ n) :
    ∃ c : Fin n ⊕ Fin 2 → Fin 4, IsProperFn (Hgraph n) c ∧ IsPlain c ∧
      ({0, 1, 2} : Set (Fin 4)) ⊆ Set.range (fun i => c (Sum.inl i)) ∧
      ∃ (j : Fin 2) (y : Fin 4), y ≠ 3 ∧ ∀ w, (Hgraph n).Adj (Sum.inr j) w → c w ≠ y :=
  rem_4_5_three_colours_move_proved n hn

/-- Section 4.2 (girth six), v4.24 l. 717-726: for `n ≥ 5`, `J_n` has `N = n + 4` vertices, it is `2`-degenerate
(order `v_1, …, v_n, a_0, …, a_3`), bipartite (odd path vertices with `a_0, a_2` against even path vertices with
`a_1, a_3`), and has girth `6`. -/
theorem sec4_Jgraph (n : ℕ) (hn : 5 ≤ n) :
    Fintype.card (Fin n ⊕ Fin 4) = n + 4 ∧
      IsDegOrder (Jgraph n) 2 (finSumFinEquiv : Fin n ⊕ Fin 4 ≃ Fin (n + 4)) ∧
      IsProperFn (Jgraph n) (sideJ n) ∧ (Jgraph n).egirth = 6 := by
  exact sec4_Jgraph_proved n hn

/-- Section 4.2, v4.24 l. 718-719: "We obtain `J_ℓ` from `H_ℓ` by splitting `a` into `a_1` and `a_3`, and `b` into `a_0`
and `a_2`, each new vertex keeping every second path neighbour of the old one": merging `a_1, a_3` into `a` and
`a_0, a_2` into `b` maps the edges of `J_ℓ` onto those of `H_ℓ`, and two consecutive path neighbours `v_i, v_{i+2}` of
an old vertex go to its two different new vertices. (The removed `4`-cycles: `sec4_Jgraph`, girth `6`.) -/
theorem sec4_J_from_H (n : ℕ) :
    (∀ u v : Fin n ⊕ Fin 2, (Hgraph n).Adj u v ↔ ∃ u' v' : Fin n ⊕ Fin 4, (Jgraph n).Adj u' v' ∧
      Sum.map id (fun k : Fin 4 => (⟨(k.val + 1) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) u' = u ∧
      Sum.map id (fun k : Fin 4 => (⟨(k.val + 1) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) v' = v) ∧
    ∀ (i : ℕ) (hi : i + 2 < n) (k k' : Fin 4), (Jgraph n).Adj (.inl ⟨i, by omega⟩) (.inr k) →
      (Jgraph n).Adj (.inl ⟨i + 2, hi⟩) (.inr k') →
      (⟨(k.val + 1) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = ⟨(k'.val + 1) % 2, Nat.mod_lt _ (by norm_num)⟩ ∧
        k ≠ k' :=
  sec4_J_from_H_proved n

/-- Section 4.2, v4.24 l. 722 (the paper's proof that the girth of `J_ℓ` is at least `6`; the Lean proof of `sec4_Jgraph`
takes another route, so these steps are rows of their own): "As the path is acyclic, every cycle contains some
`a_j`". -/
theorem sec4_J_cycle_meets_apex (n : ℕ) {u : Fin n ⊕ Fin 4} (w : (Jgraph n).Walk u u) (hw : w.IsCycle) :
    ∃ j : Fin 4, Sum.inr j ∈ w.support :=
  sec4_J_cycle_meets_apex_proved n w hw

/-- Section 4.2, v4.24 l. 722: "the `a_j` are pairwise non-adjacent". -/
theorem sec4_J_apices_nonadj (n : ℕ) (j j' : Fin 4) : ¬ (Jgraph n).Adj (Sum.inr j) (Sum.inr j') :=
  sec4_J_apices_nonadj_proved n j j'

/-- Section 4.2, v4.24 l. 722-724: "A cycle through exactly one `a_j` is `a_j v_i ⋯ v_{i'} a_j` with `i < i'` and
`i ≡ i' ≡ j (mod 4)`. Since `i' − i ≥ 4`, its length is at least `6`". -/
theorem sec4_J_one_apex_cycle (n : ℕ) {u : Fin n ⊕ Fin 4} (w : (Jgraph n).Walk u u) (hw : w.IsCycle)
    (j : Fin 4) (hj : Sum.inr j ∈ w.support) (hone : ∀ j' : Fin 4, Sum.inr j' ∈ w.support → j' = j) :
    6 ≤ w.length :=
  sec4_J_one_apex_cycle_proved n w hw j hj hone

/-- Section 4.2, v4.24 l. 724-726: "A cycle through two or more of the `a_j` has at least two path vertices between any
two of the `a_j` that are consecutive on it (each path vertex is joined to exactly one `a_j`). It therefore has at least
three vertices for each `a_j` on it, and length at least `6`". -/
theorem sec4_J_two_apex_cycle (n : ℕ) {u : Fin n ⊕ Fin 4} (w : (Jgraph n).Walk u u) (hw : w.IsCycle)
    (j j' : Fin 4) (hjj : j ≠ j') (hj : Sum.inr j ∈ w.support) (hj' : Sum.inr j' ∈ w.support) :
    6 ≤ w.length :=
  sec4_J_two_apex_cycle_proved n w hw j j' hjj hj hj'

/-- Section 4.2, v4.24 l. 726-727 ("Finally, the `6`-cycle `a_1 v_1 v_2 v_3 v_4 v_5 a_1` shows that `J_ℓ` is not a forest,
so its degeneracy is `2`"; Proposition 1.3, "degeneracy `2`", l. 84-89): `J_n` (`n ≥ 5`) is not `1`-degenerate. -/
theorem sec4_Jgraph_not_one_degenerate (n : ℕ) (hn : 5 ≤ n) : ¬ IsDegenerate (Jgraph n) 1 := by
  exact sec4_Jgraph_not_one_degenerate_proved n hn

/-- Section 4.2, v4.24 l. 726: "Finally, the `6`-cycle `a_1 v_1 v_2 v_3 v_4 v_5 a_1` shows that `J_ℓ` is not a forest".
Lean: the closed walk `a_1, v_1, …, v_5, a_1` (`a_1 = Sum.inr 1`, `v_i = Sum.inl (i-1)`) is a cycle of length `6`, so
`J_n` (`n ≥ 5`) is not acyclic. -/
theorem sec4_Jgraph_six_cycle (n : ℕ) (hn : 5 ≤ n) :
    ∃ w : (Jgraph n).Walk (.inr 1) (.inr 1), w.IsCycle ∧ w.length = 6 ∧
      w.support = [.inr 1, .inl ⟨0, by omega⟩, .inl ⟨1, by omega⟩, .inl ⟨2, by omega⟩, .inl ⟨3, by omega⟩,
        .inl ⟨4, by omega⟩, .inr 1] ∧ ¬ (Jgraph n).IsAcyclic := by
  exact sec4_Jgraph_six_cycle_proved n hn

/-- Proposition 4.6 (prop:LB6), v4.24 l. 729-731: for `n ≥ 29`, `σ⁺` and `σ⁻` (all `a_j` on `3`, `v_i` on
`±(i-1) mod 3`) are at distance at least `(n-29)²/128` in `R_4(J_n)`; hence `diam R_4(J_n) ≥ (N-33)²/128`. -/
theorem prop_4_6 (n : ℕ) (hn : 29 ≤ n) :
    (∃ σp σm : (Jgraph n).Coloring (Fin 4), ⇑σp = sigmaPlus n 4 ∧ ⇑σm = sigmaMinus n 4 ∧
      ∀ p : (recolGraph (Jgraph n) 4).Walk σp σm, ((n : ℝ) - 29) ^ 2 / 128 ≤ p.length) ∧
    ((((n + 4 : ℕ) : ℝ) - 33) ^ 2 / 128 ≤ ((recolGraph (Jgraph n) 4).diam : ℝ)) := by
  exact prop_4_6_proved n hn (Sec4Aux.hfinJ @thm_1_2_early n)

/-- Proof of Proposition 4.6, v4.24 l. 754-755: "If no `a_j` moves, at least `(ℓ-2)²/4 > (ℓ-29)²/128` moves are needed,
as for `H_ℓ`": Lean proves at least `(ℓ²-1)/4` moves and `(ℓ-2)²/4 ≤ (ℓ²-1)/4`. -/
theorem prop_4_6_no_move (n : ℕ) (hn : 29 ≤ n) (σp σm : (Jgraph n).Coloring (Fin 4))
    (hσp : ⇑σp = sigmaPlus n 4) (hσm : ⇑σm = sigmaMinus n 4) (p : (recolGraph (Jgraph n) 4).Walk σp σm)
    (hno : ∀ i < p.length, ∀ j, (p.getVert i) (.inr j) = (p.getVert (i + 1)) (.inr j)) :
    ((n : ℝ) - 2) ^ 2 / 4 ≤ ((n : ℝ) ^ 2 - 1) / 4 ∧ ((n : ℝ) ^ 2 - 1) / 4 ≤ p.length ∧
      ((n : ℝ) - 29) ^ 2 / 128 < ((n : ℝ) - 2) ^ 2 / 4 :=
  prop_4_6_no_move_proved n hn σp σm hσp hσm p hno

/-- Proposition 4.6 (prop:LB6), v4.24 l. 718 and 730-731: `J_ℓ` "has `n = ℓ + 4` vertices", and for `ℓ ≥ 29`, "Hence
`diam R_4(J_ℓ) ≥ (n−33)²/128`". The paper's `ℓ` is Lean's `l` (the `n` of `prop_4_6`); the paper's `n` is
`Fintype.card` of the vertex type. -/
theorem prop_4_6_vertices (l : ℕ) (hl : 29 ≤ l) :
    Fintype.card (Fin l ⊕ Fin 4) = l + 4 ∧
    (((Fintype.card (Fin l ⊕ Fin 4) : ℕ) : ℝ) - 33) ^ 2 / 128 ≤ ((recolGraph (Jgraph l) 4).diam : ℝ) :=
  prop_4_6_vertices_proved l hl (Sec4Aux.hfinJ @thm_1_2_early l)

/-- Lemma 4.7 (lem:flat4), v4.24 l. 737-738: if a plain colouring of `J_n` allows a move of some `a_j`, then
`|W| ≤ 3(n-1)/4 + 7`. -/
theorem lem_4_7 (n : ℕ) (c : Fin n ⊕ Fin 4 → Fin 4) (hc : IsProperFn (Jgraph n) c) (hp : IsPlain c)
    (hmove : ∃ j y, LegalMove (Jgraph n) (fun _ => univ) c (.inr j, y)) (h : ℕ → ℤ)
    (hh : IsPathHeight c h) : (|h (n - 1) - h 0| : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4 + 7 := by
  exact lem_4_7_proved n c hc hp hmove h hh

/-- Remark 4.8 (rem:Jl) (i), v4.24 l. 763-765: for `ℓ ≥ 15`, `J_ℓ`: "Its treewidth is at least `3`, since it has `K_4`
as a minor: the sets `{a_1, v_1, v_9, v_10, v_11}`, `{a_2, v_2}`, `{a_3, v_3}` and `{a_0, v_4, …, v_8}` are disjoint, each
induces a connected subgraph, and any two of them are joined by an edge" (the four sets are `Jbranch n`; minors are given
by minor models, Defs/Minor.lean). Lean takes the paper's route: a minor model of `K_m` gives treewidth at least `m - 1`
(`treewidth_ge_of_minorModel`, LB/JMinor.lean). -/
theorem rem_4_8_i (n : ℕ) (hn : 15 ≤ n) :
    IsMinorModel (⊤ : SimpleGraph (Fin 4)) (Jgraph n) (Jbranch n) ∧ HasMinor (Jgraph n) (⊤ : SimpleGraph (Fin 4)) ∧
      3 ≤ treewidth (Jgraph n) :=
  rem_4_8_i_proved n hn

/-- Remark 4.8 (ii), v4.24 l. 766: "The vertex `a_1` has degree at least `4`, with neighbours `v_1`, `v_5`, `v_9` and
`v_13`" (`a_1` = `Sum.inr 1`, `v_i` = `Sum.inl` of `i - 1`); so the maximum degree of `J_ℓ` exceeds `3`. -/
theorem rem_4_8_ii (n : ℕ) (hn : 15 ≤ n) :
    (Jgraph n).Adj (.inr 1) (.inl ⟨0, by omega⟩) ∧ (Jgraph n).Adj (.inr 1) (.inl ⟨4, by omega⟩) ∧
      (Jgraph n).Adj (.inr 1) (.inl ⟨8, by omega⟩) ∧ (Jgraph n).Adj (.inr 1) (.inl ⟨12, by omega⟩) ∧
      4 ≤ (Jgraph n).degree (.inr 1) ∧ 3 < (Jgraph n).maxDegree :=
  rem_4_8_ii_proved n hn

/-- Remark 4.8 (iii), v4.24 l. 779-785: "The graph `J_ℓ` is connected, has more than three vertices and girth `6`, and
has minimum degree at least `2`, since each `v_i` has a neighbour on the path and a neighbour `a_j`, and each `a_j` has
at least two neighbours on the path. It is not a disjoint union of cliques, so it suffices to show that no `S`, `u`, `v`
and `D` have the first three properties." Hence `J_ℓ` is not `3`-colour-dense (class (iii), l. 762). Not a disjoint union of cliques: adjacency is
not transitive on distinct vertices. No identification applies: no separator `S` and vertices `u`, `v` have the first
three properties of the definition (l. 775-778; `D` = `compMinus`). The proof follows the paper's two cases, `|D| = 1`
(a `4`-cycle) and `|D ∪ S| ≤ 3` (`S = ∅` is no separator; `S = {z}` gives a triangle), l. 781-785. -/
theorem rem_4_8_iii (n : ℕ) (hn : 15 ≤ n) :
    (Jgraph n).Connected ∧ 3 < Fintype.card (Fin n ⊕ Fin 4) ∧ (Jgraph n).egirth = 6 ∧
      (∀ i : Fin n, (∃ i' : Fin n, (Jgraph n).Adj (.inl i) (.inl i')) ∧ ∃ j : Fin 4, (Jgraph n).Adj (.inl i) (.inr j)) ∧
      (∀ j : Fin 4, ∃ i i' : Fin n, i ≠ i' ∧ (Jgraph n).Adj (.inr j) (.inl i) ∧ (Jgraph n).Adj (.inr j) (.inl i')) ∧
      (∀ x, 2 ≤ (Jgraph n).degree x) ∧
      ¬ (∀ x y z, (Jgraph n).Adj x y → (Jgraph n).Adj y z → x ≠ z → (Jgraph n).Adj x z) ∧
      (∀ (S : Set (Fin n ⊕ Fin 4)) (u v : Fin n ⊕ Fin 4), IsSeparator (Jgraph n) S → u ∉ S → v ∉ S →
        v ∉ compMinus (Jgraph n) S u → S ⊆ (Jgraph n).neighborSet v →
        ¬ ((compMinus (Jgraph n) S u).ncard = 1 ∨ (compMinus (Jgraph n) S u ∪ S).ncard ≤ 3)) ∧
      ¬ IsColourDense 3 (Jgraph n) :=
  rem_4_8_iii_proved n hn

/-- Remark 4.8 (iv), v4.24 l. 767-768: "Its Grundy number is at least `4`, since a first-fit colouring in an order that
begins with `v_1, v_4, v_5, v_10, v_7, v_8, v_9, a_1` gives these vertices the colours `1, 1, 2, 1, 1, 2, 3, 4`"
(`L` lists these eight vertices; Lean's colours start at `0`). The first part says that such an order exists. -/
theorem rem_4_8_iv (n : ℕ) (hn : 15 ≤ n) :
    let L : List (Fin n ⊕ Fin 4) := [.inl ⟨0, by omega⟩, .inl ⟨3, by omega⟩, .inl ⟨4, by omega⟩, .inl ⟨9, by omega⟩,
      .inl ⟨6, by omega⟩, .inl ⟨7, by omega⟩, .inl ⟨8, by omega⟩, .inr 1]
    (∃ ρ : Fin n ⊕ Fin 4 ≃ Fin (n + 4), L.map (fun x => (ρ x).val) = [0, 1, 2, 3, 4, 5, 6, 7]) ∧
      (∀ (ρ : Fin n ⊕ Fin 4 ≃ Fin (n + 4)) (c : Fin n ⊕ Fin 4 → ℕ), IsGreedyRel (Jgraph n) ρ c →
        L.map (fun x => (ρ x).val) = [0, 1, 2, 3, 4, 5, 6, 7] → L.map c = [0, 0, 1, 0, 0, 1, 2, 3]) ∧
      4 ≤ grundyNumber (Jgraph n) :=
  rem_4_8_iv_proved n hn

/-- Remark 4.8 (v), v4.24 l. 769-770: "As `J_ℓ` has `ℓ + 4` vertices and `2ℓ − 1` edges, its maximum average degree is
at least `2(2ℓ − 1)/(ℓ + 4) > 3`" (for `ℓ ≥ 15`). -/
theorem rem_4_8_v (n : ℕ) (hn : 15 ≤ n) :
    Fintype.card (Fin n ⊕ Fin 4) = n + 4 ∧ (Jgraph n).edgeFinset.card = 2 * n - 1 ∧
      2 * (2 * (n : ℝ) - 1) / (n + 4) ≤ mad (Jgraph n) ∧ (3 : ℝ) < 2 * (2 * (n : ℝ) - 1) / (n + 4) :=
  rem_4_8_v_proved n hn

/-- Remark 4.8, v4.24 l. 762: "For `ℓ ≥ 15`, the graph `J_ℓ` lies in none of the classes (i)-(v) of Section 1": (i)
treewidth at most `2`, (ii) maximum degree at most `3`, (iii) `3`-colour-dense, (iv) Grundy number at most `3`, (v)
maximum average degree at most `3 - ε` for a fixed `ε > 0` (here `mad > 3`). From (i)-(v) above. -/
theorem rem_4_8 (n : ℕ) (hn : 15 ≤ n) :
    2 < treewidth (Jgraph n) ∧ 3 < (Jgraph n).maxDegree ∧ ¬ IsColourDense 3 (Jgraph n) ∧
      3 < grundyNumber (Jgraph n) ∧ 3 < mad (Jgraph n) :=
  ⟨(rem_4_8_i n hn).2.2, (rem_4_8_ii n hn).2.2.2.2.2, (rem_4_8_iii n hn).2.2.2.2.2.2.2.2, (rem_4_8_iv n hn).2.2,
    lt_of_lt_of_le (rem_4_8_v n hn).2.2.2 (rem_4_8_v n hn).2.2.1⟩

/-! ## Section 5 — Open problems (the claims made there) -/

/-- Open problem 1, v4.24 l. 816-818: by Lemma 2.5 the Cereceda conjecture for `d = 2` would follow from a bound
`O(m)` on the length of a shortest sequence for every instance with `g = 0`. -/
theorem open_1_reduction (lam : ℝ)
    (hlin : ∀ (W : Type) [Fintype W] [DecidableEq W] (I : Instance W), I.g = 0 →
      ∀ α β : W → Fin 4, I.IsGreedy I.x α → I.IsGreedy I.g β →
        ∃ ms, I.IsSeq α ms β ∧ (ms.length : ℝ) ≤ lam * Fintype.card W) :
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsDegenerate G 2 → (recolGraph G 4).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞) := by
  refine open_1_reduction_of ?_ ?_ lam hlin
  · intro V _ _ G _ d; exact sec2_order_iff_degenerate_proved G d
  · intro 𝒞 lam hlam hlin V _ _ G _ n ρ hρ hc; exact lem_2_5 𝒞 lam hlam hlin G ρ hρ hc

/-- Open problem 1, v4.24 l. 816-818 ("By Lemma 2.5, a positive answer would prove Conjecture 1.1 for `d = 2`"): with
every `k ≥ 4`, i.e. the conjecture for `d = 2` exactly as in Conjecture 1.1
(`CerecedaConjectureOn AllGraphs 2`; `k = 4` is `open_1_reduction`, `k ≥ 5` is [Cer07, Thm. 5.22]). -/
theorem open_1_reduction_all_k (lam : ℝ)
    (hlin : ∀ (W : Type) [Fintype W] [DecidableEq W] (I : Instance W), I.g = 0 →
      ∀ α β : W → Fin 4, I.IsGreedy I.x α → I.IsGreedy I.g β →
        ∃ ms, I.IsSeq α ms β ∧ (ms.length : ℝ) ≤ lam * Fintype.card W) :
    CerecedaConjectureOn AllGraphs 2 :=
  intro_only_k4_open (open_1_reduction lam hlin)

/-- Open problem 1, v4.24 l. 819-827: the instance `ex8` is the instance written out there (the sink `s` with the list
`{0,1}` and `x = 1`; `u₁, …, u₇` in instance order, `u_i` = `i`, `s` = `0`; `N⁺(u₁) = N⁺(u₂) = {s}`, `N⁺(u₃) = {u₁}`,
`N⁺(u₄) = {u₂, u₃}`, `N⁺(u₅) = N⁺(u₆) = {u₄}`, `N⁺(u₇) = {u₃, u₆}`; `L(u₁) = L(u₂) = L(u₅) = {0,1,2}`,
`L(u₃) = {0,2,3}`, `L(u₆) = {1,2,3}`, `L(u₄) = L(u₇) = {0,1,2,3}`), and it contains the 5-cycle `s u₁ u₃ u₄ u₂ s`. -/
theorem open_1_five_cycle :
    ex8.graph.Adj 0 1 ∧ ex8.graph.Adj 1 3 ∧ ex8.graph.Adj 3 4 ∧ ex8.graph.Adj 4 2 ∧ ex8.graph.Adj 2 0 ∧
    [(0 : Fin 8), 1, 3, 4, 2].Nodup :=
  open_1_five_cycle_proved

/-- Open problem 1, v4.24 l. 819-828 ("two moves per vertex are not always enough. Take the sink `s` ... This instance
contains the `5`-cycle `s u₁ u₃ u₄ u₂ s`. In every sequence from `α` to `β` some vertex moves at least three times
[G, Remark 34.9]"; the instance is `ex8`, written out in `open_1_five_cycle`, which also gives the `5`-cycle; the paper
cites [G] for the last claim, Lean proves it): the instance `ex8` (`g = 0`, single-sink, `8` vertices) is not
bipartite, and NO sequence from `α` to `β` moves every vertex at most twice. -/
theorem open_1_two_moves_fail :
    ex8.NoRoots ∧ ex8.g = 0 ∧ Fintype.card (Fin 8) = 8 ∧ ¬ ex8.graph.IsBipartite ∧
    ∀ α β : Fin 8 → Fin 4, ex8.IsGreedy ex8.x α → ex8.IsGreedy ex8.g β →
      ¬ ∃ ms, ex8.IsSeq α ms β ∧ ∀ v, movesOf ms v ≤ 2 := by
  exact open_1_two_moves_fail_proved

/-- Open problem 2, v4.24 l. 832-835: "each `a_j` (`0 ≤ j < p`) is joined to the path vertices `v_i` with
`i ≡ j (mod p)`" (the graph is `spacedGraph ℓ p`), and "if `i + p + 1 ≤ ℓ` and `j ≡ i (mod p)`, then
`a_j v_i v_{i+1} a_{j+1} v_{i+p+1} v_{i+p} a_j` is a cycle of length `6`, where `a_p` means `a_0`". For `p ≥ 2` and `1 ≤ i`, the six vertices
are distinct and consecutive ones (cyclically) are adjacent. The paper's `ℓ` is Lean's `n`. -/
theorem open_2_six_cycle (n p : ℕ) (hp : 2 ≤ p) (i : ℕ) (hi : 1 ≤ i) (hin : i + p + 1 ≤ n) :
    let G := spacedGraph n p (by omega)
    let aj : Fin n ⊕ Fin p := .inr ⟨i % p, Nat.mod_lt _ (by omega)⟩
    let aj1 : Fin n ⊕ Fin p := .inr ⟨(i + 1) % p, Nat.mod_lt _ (by omega)⟩
    let vi : Fin n ⊕ Fin p := .inl ⟨i - 1, by omega⟩
    let vi1 : Fin n ⊕ Fin p := .inl ⟨i, by omega⟩
    let vip1 : Fin n ⊕ Fin p := .inl ⟨i + p, by omega⟩
    let vip : Fin n ⊕ Fin p := .inl ⟨i + p - 1, by omega⟩
    G.Adj aj vi ∧ G.Adj vi vi1 ∧ G.Adj vi1 aj1 ∧ G.Adj aj1 vip1 ∧ G.Adj vip1 vip ∧ G.Adj vip aj ∧
      [aj, vi, vi1, aj1, vip1, vip].Nodup :=
  open_2_six_cycle_proved n p hp i hi hin
/-- Open problem 2, v4.24 l. 831-834: "We cannot extend the construction of Section 4.2 to girth `7` by changing the
spacing. If, for a spacing `p ≥ 2`, each `a_j` (`0 ≤ j < p`) is joined to the path vertices `v_i` with `i ≡ j (mod p)`,
then the girth is at most `6` once `ℓ ≥ p + 2`": for `p ≥ 2` and `ℓ ≥ p + 2`, the graph `spacedGraph ℓ p` has a cycle of length at most `6` (`egirth`,
the length of a shortest cycle, `⊤` if there is none, is at most `6`); the cycle is the one of `open_2_six_cycle` with
`i = 1`. The paper's `ℓ` is Lean's `n`. -/
theorem open_2_girth (n p : ℕ) (hp : 2 ≤ p) (hn : p + 2 ≤ n) : (spacedGraph n p (by omega)).egirth ≤ 6 :=
  open_2_girth_proved n p hp hn

/-- Open problem 2, v4.24 l. 842-844: "`J_ℓ`, of girth `6`, has `ℓ + 4` vertices and `2ℓ − 1 > 3(ℓ+2)/2` edges", for
`ℓ ≥ 9` ("they are not planar for `ℓ ≥ 9`"; `3(ℓ+2)/2 = 3(n-2)/2` with `n = ℓ + 4`). The paper's `ℓ` is Lean's `n`; the counts hold for every `n`: the path
has `n − 1` edges and each path vertex one edge to an `a_j`. Girth `6` is `sec4_Jgraph`; the planar edge bound (Euler's
formula) and so the non-planarity of `J_ℓ` are not formalized. -/
theorem open_2_Jgraph_counts (n : ℕ) :
    Fintype.card (Fin n ⊕ Fin 4) = n + 4 ∧ (Jgraph n).edgeFinset.card = 2 * n - 1 ∧
      (9 ≤ n → 3 * ((n : ℝ) + 2) / 2 < 2 * n - 1) :=
  ⟨FactsAux.Jgraph_card n, by rw [FactsAux.pathApex_edges]; omega, fun h => by
    have : (9 : ℝ) ≤ n := by exact_mod_cast h
    linarith⟩

/-- Open problem 3, v4.24 l. 845-846 (the bounds `n²/8 - O(n) ≤ ρ(n) ≤ 2n² + O(n)`), as limits: the leading terms of the
bounds `2n(n+1)` (Theorem 1.2) and `(N-7)²/8` (Proposition 1.3) are `2n²` and `N²/8`. -/
theorem open_3_limits :
    Filter.Tendsto (fun n : ℕ => (2 * n * (n + 1) : ℝ) / (n : ℝ) ^ 2) Filter.atTop (nhds 2) ∧
    Filter.Tendsto (fun N : ℕ => ((N : ℝ) - 7) ^ 2 / 8 / (N : ℝ) ^ 2) Filter.atTop (nhds (1 / 8)) := by
  exact open_3_limits_proved

/-! ## Main results of Section 1, assembled from the sections below them -/

/-- Theorem 1.2 (thm:bip), v4.24 l. 80-82: for every bipartite graph `G` on `n` vertices of degeneracy at most `2`,
`R_4(G)` is connected and `diam R_4(G) ≤ 2n(n+1)`. -/
theorem thm_1_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) (hdeg : IsDegenerate G 2) :
    (recolGraph G 4).Connected ∧
      (recolGraph G 4).ediam ≤ ((2 * Fintype.card V * (Fintype.card V + 1) : ℕ) : ℕ∞) :=
  ⟨Misc.recolGraph_connected_of_ediam_le G 4 _ (hbip.mono (by norm_num)) (thm_1_2_early G hbip hdeg),
    thm_1_2_early G hbip hdeg⟩

/-- Section 1, v4.24 l. 232-235: "The union of the classes (i)-(v) does not contain all bipartite `2`-degenerate graphs.
For `ℓ ≥ 15`, the bipartite graph `J_ℓ` of girth `6` in Section 4.2, a path on `ℓ` vertices with `a_0, …, a_3`, lies in
none of them (Remark 4.8)": `J_n` (`Jgraph n`, the same graph) for `n ≥ 15` is bipartite, `2`-degenerate and
of girth `6` (`sec4_Jgraph`), and lies in none of (i)-(v) (`rem_4_8`). -/
theorem intro_Jgraph_in_no_class (n : ℕ) (hn : 15 ≤ n) :
    (Jgraph n).IsBipartite ∧ IsDegenerate (Jgraph n) 2 ∧ (Jgraph n).egirth = 6 ∧
      2 < treewidth (Jgraph n) ∧ 3 < (Jgraph n).maxDegree ∧ ¬ IsColourDense 3 (Jgraph n) ∧
      3 < grundyNumber (Jgraph n) ∧ 3 < mad (Jgraph n) :=
  ⟨Sec4Aux.Jgraph_bipartite n, Sec4Aux.Jgraph_degenerate n, (sec4_Jgraph n (by omega)).2.2.2, rem_4_8 n hn⟩

/-- Section 1, v4.24 l. 235-236: "For `ℓ ≥ 29` these graphs give the lower bound for girth `6` in Proposition 1.3, so
on them the bound of Theorem 1.2 has the best possible order `n²`": with `n = ℓ + 4` vertices, `diam R_4(J_ℓ) ≤ 2n(n+1)` (Theorem 1.2),
and `diam R_4(J_ℓ) ≥ (n-33)²/128` for `ℓ ≥ 29` (Proposition 4.6; it is the girth-`6` part of `prop_1_3`). Lean's `n` is the paper's `ℓ`; the upper bound holds for every `n`, so Lean needs no `ℓ ≥ 15`. -/
theorem intro_Jgraph_best_order (n : ℕ) :
    (recolGraph (Jgraph n) 4).ediam ≤ ((2 * (n + 4) * (n + 4 + 1) : ℕ) : ℕ∞) ∧
      (29 ≤ n → (((n + 4 : ℕ) : ℝ) - 33) ^ 2 / 128 ≤ ((recolGraph (Jgraph n) 4).diam : ℝ)) := by
  refine ⟨?_, fun h => (prop_4_6 n h).2⟩
  have h := (thm_1_2 (Jgraph n) (Sec4Aux.Jgraph_bipartite n) (Sec4Aux.Jgraph_degenerate n)).2
  rwa [FactsAux.Jgraph_card n] at h

/-- Abstract, v4.24 l. 43-46 ("For the upper bound, we fix an ordering of the vertices in which each vertex has at most
two later neighbours. In `n` stages, we transform any proper `4`-colouring into the colouring in which every vertex has
the least colour not used by its later neighbours, recolouring each vertex at most twice per stage"). (For bipartite `G` of degeneracy at most `2`: an order `ρ` and a colouring `γ` such that every proper
`4`-colouring reaches `γ` by `n` blocks of moves, each block moving every vertex at most twice; `γ` is the colouring in
which every vertex has the least colour not used by its later neighbours (v4.24 l. 130 and 135-136); block `t` moves
only vertices of the cone `C_t` of the `t`-th vertex (v4.24 l. 131-133, "Making `v_t` greedy may force us to move
earlier vertices too ... But only the cone of `v_t` is involved").) -/
theorem abstract_steps {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) (hdeg : IsDegenerate G 2) :
    ∃ (ρ : V ≃ Fin (Fintype.card V)) (γ : V → Fin 4), IsDegOrder G 2 ρ ∧
      (∀ v, IsLeastFree univ ((laterNbrs G ρ v).image γ) (γ v)) ∧
      ∀ c : V → Fin 4, IsProperFn G c → ∃ steps : List (List (V × Fin 4)),
        steps.length = Fintype.card V ∧ IsSeq G (fun _ => univ) c steps.flatten γ ∧
        (∀ ms ∈ steps, ∀ v, movesOf ms v ≤ 2) ∧
        ∀ t (ht : t < Fintype.card V), ∀ m ∈ steps.getD t [], m.1 ∈ cone G ρ (ρ.symm ⟨t, ht⟩) := by
  exact abstract_steps_proved G hbip hdeg

/-- Abstract and Section 1 (v4.24 l. 42, l. 51): the Cereceda conjecture holds for the class of bipartite graphs of
degeneracy at most `2` with `k = 4` (`R_4(G)` connected and `diam R_4(G) = O(n²)`, with the constant `4`). Every
`k ≥ 4`: `cereceda_bipartite_two_degenerate_all_k`. -/
theorem cereceda_bipartite_two_degenerate :
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsBipartite → IsDegenerate G 2 →
        (recolGraph G 4).Connected ∧ (recolGraph G 4).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞) := by
  obtain ⟨C, hC⟩ := cereceda_bipartite_two_degenerate_of (by
    intro V _ _ G _ hbip hdeg
    exact (thm_1_2 G hbip hdeg).2)
  refine ⟨C, ?_⟩
  intro V _ _ G _ hbip hdeg
  exact ⟨(thm_1_2 G hbip hdeg).1, hC V G hbip hdeg⟩

/-- Abstract and Section 1 (v4.24 l. 39-42, 51-55, 110-111): the conjecture (every `k ≥ d + 2`) holds
for bipartite graphs of degeneracy at most `2`: for EVERY `k ≥ 4`, `R_k(G)` is connected and `diam R_k(G) = O(n²)`.
`k = 4` is Theorem 1.2; `k ≥ 5 = 2d + 1` is [Cer07, Thm. 5.22] (cited: `Cited.cer07_thm522`). -/
theorem cereceda_bipartite_two_degenerate_all_k :
    ∀ k : ℕ, 4 ≤ k → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsBipartite → IsDegenerate G 2 →
        (recolGraph G k).Connected ∧ (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞) := by
  intro k hk
  rcases eq_or_lt_of_le hk with rfl | hk5
  · exact cereceda_bipartite_two_degenerate
  · obtain ⟨C, hC⟩ := Cited.cer07_thm522 2 k (by omega) (by omega)
    refine ⟨C, ?_⟩
    intro V _ _ G _ hbip hdeg
    exact ⟨Misc.recolGraph_connected_of_ediam_le G k _ (hbip.mono (by omega)) (hC V G hdeg), hC V G hdeg⟩

/-- Abstract and Section 1 (v4.24 l. 42, "hence the conjecture holds for these graphs"), checked against
the definition of the conjecture word for word: Conjecture 1.1 restricted to the class of bipartite graphs of
degeneracy at most `2`, for every `d ≥ 1` (`d = 1`: [Cer07, Thm. 5.22] for every `k ≥ 3`; `d ≥ 2`: the class is
`2`-degenerate and `k ≥ 4`, so `cereceda_bipartite_two_degenerate_all_k`). -/
theorem cereceda_conjecture_on_class : ∀ d : ℕ, 1 ≤ d → CerecedaConjectureOn BipTwoDegenerate d := by
  intro d hd k hk
  rcases (by omega : d = 1 ∨ 2 ≤ d) with rfl | hd2
  · obtain ⟨C, hC⟩ := Cited.cer07_thm522 1 k (by omega) (by omega)
    exact ⟨C, by intro V _ _ G _ _ hG; exact hC V G hG⟩
  · obtain ⟨C, hC⟩ := cereceda_bipartite_two_degenerate_all_k k (by omega)
    exact ⟨C, by intro V _ _ G _ hP _; exact (hC V G hP.1 hP.2).2⟩

/-- Section 1, v4.24 l. 117-125 ("With Theorem 1.2, the conjecture holds for all planar bipartite graphs", l. 124: for
all `d ≥ 1` and `k ≥ d+2`, `diam R_k(G) = O(n²)` for every planar bipartite `d`-degenerate graph `G` on `n` vertices), in
a planarity-free form. Mathlib has no planar graphs, so two facts about planar bipartite graphs are hypotheses about the
class `Cls`, and are NOT FORMALIZED for planar graphs (AUDIT_NOTES): its graphs are bipartite and `3`-degenerate
(Euler's formula, l. 117), and `diam R_5(G) ≤ 4n²` ([BH22, Thm. 2], cited, l. 117-118; the paper writes `O(n²)`, and
`4n²` is the bound stated in [BH22]). The case deduction of the paper is PROVED for EVERY such class and every
`d ≥ 1`: `d ≥ 3` (degeneracy `3`):
`k = 5` is [BH22, Thm. 2], `k ≥ 6 = (3/2)(3+1)` is [BH22, Thm. 1] (cited: `Cited.bh22_thm1_quadratic`); `d = 2`: `k = 4`
is Theorem 1.2 and `k ≥ 5` is [Cer07, Thm. 5.22]; `d = 1`: [Cer07, Thm. 5.22] (cited: `Cited.cer07_thm522`).
GIVEN NOT-FORMALIZED INPUT: `hcls` (planar bipartite graphs are bipartite and 3-degenerate, by Euler's formula) and `hbh2` ([BH22, Theorem 2] for planar bipartite graphs, a cited result about planar graphs). -/
theorem intro_planar_bipartite_deduction
    (Cls : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], Prop)
    (hcls : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], Cls V G →
      G.IsBipartite ∧ IsDegenerate G 3)
    (hbh2 : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], Cls V G →
      (recolGraph G 5).ediam ≤ ((4 * Fintype.card V ^ 2 : ℕ) : ℕ∞)) :
    ∀ d : ℕ, 1 ≤ d → CerecedaConjectureOn Cls d := by
  intro d hd k hk
  rcases (by omega : d = 1 ∨ d = 2 ∨ 3 ≤ d) with rfl | rfl | hd3
  · obtain ⟨C, hC⟩ := Cited.cer07_thm522 1 k (by omega) (by omega)
    exact ⟨C, by intro V _ _ G _ _ hG; exact hC V G hG⟩
  · obtain ⟨C, hC⟩ := cereceda_bipartite_two_degenerate_all_k k (by omega)
    exact ⟨C, by intro V _ _ G _ hP hG; exact (hC V G (hcls V G hP).1 hG).2⟩
  · rcases (by omega : k = 5 ∨ 6 ≤ k) with rfl | hk6
    · exact ⟨4, by intro V _ _ G _ hP _; exact hbh2 V G hP⟩
    · obtain ⟨C, hC⟩ := Cited.bh22_thm1_quadratic 3 k (by omega)
      exact ⟨C, by intro V _ _ G _ hP _; exact hC V G (hcls V G hP).2⟩

/-- Section 1, v4.24 l. 124-125: "To our knowledge, the case `d = 2`, `k = 4` was the only one still open": every
other case of the planar bipartite statement follows from the cited results alone (no Theorem 1.2): `d = 1` and `d = 2`,
`k ≥ 5` from [Cer07, Thm. 5.22]; `d ≥ 3`: `k = 5` from [BH22, Thm. 2] and `k ≥ 6` from [BH22, Thm. 1]. The same
planarity-free form as `intro_planar_bipartite_deduction`. The case `d = 3` is also l. 118-119: "Cranston and Mahmoud
noted that this result settles the case of degeneracy `3` [CM24]".
GIVEN NOT-FORMALIZED INPUT: `hcls` (planar bipartite graphs are bipartite and 3-degenerate, by Euler's formula) and `hbh2` ([BH22, Theorem 2] for planar bipartite graphs, a cited result about planar graphs). -/
theorem intro_planar_known_cases
    (Cls : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], Prop)
    (hcls : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], Cls V G →
      G.IsBipartite ∧ IsDegenerate G 3)
    (hbh2 : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], Cls V G →
      (recolGraph G 5).ediam ≤ ((4 * Fintype.card V ^ 2 : ℕ) : ℕ∞)) :
    ∀ d k : ℕ, 1 ≤ d → d + 2 ≤ k → (d, k) ≠ (2, 4) → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], Cls V G → IsDegenerate G d →
        (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞) := by
  intro d k hd hk hne
  rcases (by omega : d = 1 ∨ d = 2 ∨ 3 ≤ d) with rfl | rfl | hd3
  · obtain ⟨C, hC⟩ := Cited.cer07_thm522 1 k (by omega) (by omega)
    exact ⟨C, by intro V _ _ G _ _ hG; exact hC V G hG⟩
  · have hk4 : k ≠ 4 := fun h => hne (by rw [h])
    obtain ⟨C, hC⟩ := Cited.cer07_thm522 2 k (by omega) (by omega)
    exact ⟨C, by intro V _ _ G _ _ hG; exact hC V G hG⟩
  · rcases (by omega : k = 5 ∨ 6 ≤ k) with rfl | hk6
    · exact ⟨4, by intro V _ _ G _ hP _; exact hbh2 V G hP⟩
    · obtain ⟨C, hC⟩ := Cited.bh22_thm1_quadratic 3 k (by omega)
      exact ⟨C, by intro V _ _ G _ hP _; exact hC V G (hcls V G hP).2⟩

/-- Open problem 2, v4.24 l. 838-839: "Planar graphs of girth at least `6` are `2`-degenerate, and Theorem 1.2 gives
`diam R_4(G) = O(n²)` for those that are bipartite", in a planarity-free form: for any class `Cls` of `2`-degenerate
graphs (the hypothesis `hcls`; for planar graphs of girth at least `6` it is Euler's formula, NOT FORMALIZED), Theorem
1.2 gives `diam R_4(G) ≤ 2n(n+1)` for its bipartite members.
GIVEN NOT-FORMALIZED INPUT: `hcls` (planar graphs of girth at least 6 are 2-degenerate, by Euler's formula). -/
theorem open_2_planar_girth6
    (Cls : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], Prop)
    (hcls : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], Cls V G →
      IsDegenerate G 2) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], Cls V G → G.IsBipartite →
      (recolGraph G 4).ediam ≤ ((2 * Fintype.card V * (Fintype.card V + 1) : ℕ) : ℕ∞) := by
  intro V _ _ G _ hP hbip
  exact (thm_1_2 G hbip (hcls V G hP)).2

/-- Support for `prop_1_3` (not a row): the `ℓ`-forms of the lower bounds for `H_ℓ` and `J_ℓ` (Propositions 4.1 and
4.6, v4.24 l. 631-635 and 729-731, with the facts of Section 4 about the two families). -/
private theorem prop_1_3_lforms :
    (∀ n : ℕ, 5 ≤ n →
      (Hgraph n).IsBipartite ∧ IsStraightLinePlanar (Hgraph n) ∧
      IsDegenerate (Hgraph n) 2 ∧ ¬ IsDegenerate (Hgraph n) 1 ∧
      Fintype.card (Fin n ⊕ Fin 2) = n + 2 ∧
      ((((n + 2 : ℕ) : ℝ) - 7) ^ 2 / 8 ≤ ((recolGraph (Hgraph n) 4).diam : ℝ))) ∧
    (∀ n : ℕ, 29 ≤ n →
      (Jgraph n).IsBipartite ∧ IsDegenerate (Jgraph n) 2 ∧ ¬ IsDegenerate (Jgraph n) 1 ∧
      (Jgraph n).egirth = 6 ∧ Fintype.card (Fin n ⊕ Fin 4) = n + 4 ∧
      ((((n + 4 : ℕ) : ℝ) - 33) ^ 2 / 128 ≤ ((recolGraph (Jgraph n) 4).diam : ℝ))) := by
  exact prop_1_3_lforms_proved @thm_1_2_early

/-- Support for `prop_1_3` (not a row): `R_4(H_ℓ)` and `R_4(J_ℓ)` are connected (Theorem 1.2), so their diameters are
true distances (Mathlib's `diam` is `0` only for disconnected graphs). -/
private theorem prop_1_3_connected :
    (∀ n : ℕ, 5 ≤ n → (recolGraph (Hgraph n) 4).Connected) ∧
      ∀ n : ℕ, 29 ≤ n → (recolGraph (Jgraph n) 4).Connected := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨hb, -, hd, -⟩ := prop_1_3_lforms.1 n hn
    exact (thm_1_2 (Hgraph n) hb hd).1
  · obtain ⟨hb, hd, -⟩ := prop_1_3_lforms.2 n hn
    exact (thm_1_2 (Jgraph n) hb hd).1

/-- Proposition 1.3 (prop:lb), v4.24 l. 84-89, with `n` the number of vertices: for every `n ≥ 7` a planar
(straight-line) bipartite graph of degeneracy `2` on `n` vertices with `diam R_4 ≥ (n-7)²/8` (it is `H_{n-2}`), and for
every `n ≥ 33` a bipartite graph of degeneracy `2` and girth `6` on `n` vertices with `diam R_4 ≥ (n-33)²/128` (it is
`J_{n-4}`); in both, `R_4` is connected. -/
theorem prop_1_3 :
    (∀ n : ℕ, 7 ≤ n → ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      Fintype.card V = n ∧ G.IsBipartite ∧ IsStraightLinePlanar G ∧ IsDegenerate G 2 ∧ ¬ IsDegenerate G 1 ∧
        (recolGraph G 4).Connected ∧ ((n : ℝ) - 7) ^ 2 / 8 ≤ ((recolGraph G 4).diam : ℝ)) ∧
    (∀ n : ℕ, 33 ≤ n → ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      Fintype.card V = n ∧ G.IsBipartite ∧ IsDegenerate G 2 ∧ ¬ IsDegenerate G 1 ∧ G.egirth = 6 ∧
        (recolGraph G 4).Connected ∧ ((n : ℝ) - 33) ^ 2 / 128 ≤ ((recolGraph G 4).diam : ℝ)) := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨hb, hpl, hd, hd1, hc, hl⟩ := prop_1_3_lforms.1 (n - 2) (by omega)
    have he : n - 2 + 2 = n := by omega
    refine ⟨Fin (n - 2) ⊕ Fin 2, inferInstance, inferInstance, Hgraph (n - 2), inferInstance,
      by rw [hc, he], hb, hpl, hd, hd1, prop_1_3_connected.1 (n - 2) (by omega), ?_⟩
    rw [he] at hl
    exact hl
  · obtain ⟨hb, hd, hd1, hg, hc, hl⟩ := prop_1_3_lforms.2 (n - 4) (by omega)
    have he : n - 4 + 4 = n := by omega
    refine ⟨Fin (n - 4) ⊕ Fin 4, inferInstance, inferInstance, Jgraph (n - 4), inferInstance,
      by rw [hc, he], hb, hd, hd1, hg, prop_1_3_connected.2 (n - 4) (by omega), ?_⟩
    rw [he] at hl
    exact hl

/-- Open problem 3, v4.24 l. 845-846, upper half `ρ(n) ≤ 2n² + O(n)`: every bipartite graph `G` on `n` vertices of
degeneracy at most `2` has `diam R_4(G) ≤ 2n² + 2n` (connectivity included: `ediam`). -/
theorem open_3_rho_upper (n : ℕ) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Fintype.card V = n) (hbip : G.IsBipartite) (hdeg : IsDegenerate G 2) :
    (recolGraph G 4).ediam ≤ ((2 * n ^ 2 + 2 * n : ℕ) : ℕ∞) := by
  have h := (thm_1_2 G hbip hdeg).2
  rw [hn] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  ring

/-- Open problem 3, v4.24 l. 845-846, lower half `n²/8 - O(n) ≤ ρ(n)`: for every `n` there is a bipartite graph `G`
on `n` vertices of degeneracy at most `2` with `diam R_4(G) ≥ n²/8 - 2n` (`H_{n-2}` for `n ≥ 7`). -/
theorem open_3_rho_lower (n : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      Fintype.card V = n ∧ G.IsBipartite ∧ IsDegenerate G 2 ∧
        (n : ℝ) ^ 2 / 8 - 2 * n ≤ ((recolGraph G 4).diam : ℝ) := by
  rcases lt_or_ge n 7 with hn | hn
  · refine ⟨Fin n, inferInstance, inferInstance, ⊥, inferInstance, by simp, ?_, ?_, ?_⟩
    · exact ⟨SimpleGraph.Coloring.mk (fun _ => 0) (fun h => h.elim)⟩
    · intro s ⟨v, hv⟩
      exact ⟨v, hv, by simp⟩
    · have h1 : (n : ℝ) ≤ 6 := by exact_mod_cast (by omega : n ≤ 6)
      have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h3 : (0 : ℝ) ≤ ((recolGraph (⊥ : SimpleGraph (Fin n)) 4).diam : ℝ) := Nat.cast_nonneg _
      nlinarith
  · obtain ⟨hb, -, hd, -, hc, hl⟩ := (prop_1_3_lforms).1 (n - 2) (by omega)
    refine ⟨Fin (n - 2) ⊕ Fin 2, inferInstance, inferInstance, Hgraph (n - 2), inferInstance,
      by rw [hc]; omega, hb, hd, le_trans ?_ hl⟩
    have he : n - 2 + 2 = n := by omega
    rw [he]
    have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

end Cereceda
