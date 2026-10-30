import CCO.RelationalCompletion.Atomic.Class
import CCO.RelationalCompletion.Atomic.BoundariesTwoColour

/-! The finite clique counterexamples are actual instances of the atomic
class interfaces, rather than unrelated cardinality models. -/
set_option backward.isDefEq.respectTransparency.types false

namespace CCO.RelationalCompletion.Atomic.Boundaries
open SimpleGraph

/-- One unary type and one symmetric irreflexive diversity atom. -/
def onePalette : Palette.{0,0} where
  Sorts := Unit
  Atom := Unit
  src _ := ()
  tgt _ := ()
  conv _ := ()
  conv_conv _a := Subsingleton.elim _ _
  src_conv _ := rfl
  tgt_conv _ := rfl

/-- The literal complete one-colour model. -/
def clique (n : Nat) : Model onePalette where
  size := n
  diagram := {
    tag _ := ()
    edge x y := if x = y then none else some ()
    edge_self _ := by simp
    edge_reverse x y := by
      by_cases h : x = y
      · subst y; simp
      · simp [h, Ne.symm h, onePalette]
    typed _ _ _ _ := ⟨rfl, rfl⟩ }
  complete x y h := ⟨(), by simp [h]⟩

/-- Completeness and the singleton atom force the exact edge table. -/
theorem onePalette_edge (A : Model onePalette) (x y : Fin A.size) :
    A.edge x y = if x = y then none else some () := by
  split_ifs with h
  · subst y; exact A.diagram.edge_self x
  · obtain ⟨a, ha⟩ := A.complete x y h
    have hu : a = (() : onePalette.Atom) := by cases a; rfl
    rw [hu] at ha
    exact ha

/-- Every injection between one-colour complete models is an induced embedding. -/
def oneEmbedding (A B : Model onePalette) (e : Fin A.size ↪ Fin B.size) : Embedding A B where
  vertex := e
  tag_eq _ := by change (_ : Unit) = _; exact Subsingleton.elim _ _
  edge_eq x y := by
    rw [onePalette_edge, onePalette_edge]
    simp only [e.injective.eq_iff]

/-- Exact isomorphism-closed age of the finite k-point complete graph. -/
def cliqueAge (k : Nat) (A : Model onePalette) : Prop := A.size ≤ k

theorem cliqueAge_hereditary (k : Nat) : Hereditary (cliqueAge k) := by
  intro A B ⟨e⟩ hB
  have h := Fintype.card_le_of_embedding e.vertex
  simp only [Fintype.card_fin] at h
  exact h.trans hB

theorem cliqueAge_AP (k : Nat) : AP (cliqueAge k) := by
  intro C A B hC hA hB l r
  obtain ⟨t, ht, f, g, hfg⟩ := completeAge_AP hA hB l.vertex r.vertex
  exact ⟨clique t, ht, oneEmbedding A (clique t) f, oneEmbedding B (clique t) g, hfg⟩

theorem cliqueFour_small : SmallSubmodels (cliqueAge 3) (clique 4) := by
  intro n e hn
  exact hn

theorem cliqueFour_not_mem : ¬cliqueAge 3 (clique 4) := by
  change ¬ (4 ≤ 3)
  omega

theorem cliqueFour_no_hom :
    ¬∃ B : Model onePalette, cliqueAge 3 B ∧ Nonempty (Hom (clique 4).diagram B) := by
  rintro ⟨B, hB, ⟨f⟩⟩
  have h := Fintype.card_le_of_embedding f.toEmbedding.vertex
  simp only [Fintype.card_fin] at h
  change 4 ≤ B.size at h
  change B.size ≤ 3 at hB
  omega

/-- Underlying specified-edge graph of a one-colour partial diagram. -/
def diagramGraph {n : Nat} (D : Diagram onePalette n) : SimpleGraph (Fin n) where
  Adj x y := D.edge x y = some ()
  symm := ⟨by
    intro x y h
    rw [D.edge_reverse, h]
    rfl⟩
  loopless := ⟨by intro x h; rw [D.edge_self] at h; contradiction⟩

theorem cyclicNext_eq_add {m : Nat} [NeZero m] (hm : 3 ≤ m) (i : Fin m) :
    cyclicNext (by omega) i = i + 1 := by
  apply Fin.ext
  simp only [cyclicNext, Fin.val_mk, Fin.val_add, Fin.val_one']
  rw [Nat.mod_eq_of_lt (show 1 < m by omega)]

theorem cycleGraph_next_adj {m : Nat} (hm : 3 ≤ m) (i : Fin m) :
    (cycleGraph m).Adj i (cyclicNext (by omega) i) := by
  let : NeZero m := ⟨by omega⟩
  rw [cyclicNext_eq_add hm]
  rcases m with _ | _ | k
  · omega
  · omega
  ·
    rw [SimpleGraph.cycleGraph_adj]
    exact Or.inr (by simp)

theorem cycleGraph_adj_or_next {m : Nat} (hm : 3 ≤ m) {i j : Fin m}
    (h : (cycleGraph m).Adj i j) :
    j = cyclicNext (by omega) i ∨ i = cyclicNext (by omega) j := by
  let : NeZero m := ⟨by omega⟩
  rw [cyclicNext_eq_add hm, cyclicNext_eq_add hm]
  rcases m with _ | _ | k
  · omega
  · omega
  ·
    rw [SimpleGraph.cycleGraph_adj] at h
    rcases h with h | h
    · exact Or.inr (by have hh := sub_eq_iff_eq_add.mp h; simpa only [add_comm] using hh)
    · exact Or.inl (by have hh := sub_eq_iff_eq_add.mp h; simpa only [add_comm] using hh)

/-- All simple cycles of the K4 input are feasible in the actual Atomic class. -/
theorem cliqueFour_cycles : ∀ C : SimpleCycle (clique 4).diagram,
    ∃ B : Model onePalette, cliqueAge 3 B ∧ CycleHomInto C B := by
  intro C
  let c := SimpleGraph.cycleGraph.tricoloring C.length (by have := C.length_ge_three; omega)
  refine ⟨clique 3, le_rfl, c, (fun _ => rfl), ?_⟩
  intro p a ha
  have hn := c.valid (cycleGraph_next_adj C.length_ge_three p)
  cases a
  exact if_neg hn

/-- A graph-theoretic simple closed walk gives the literal specified Atomic cycle. -/
def walkSimpleCycle {n : Nat} (D : Diagram onePalette n) {x : Fin n}
    (p : (diagramGraph D).Walk x x) (hp : p.IsCycle) : SimpleCycle D where
  length := p.length
  length_ge_three := hp.three_le_length
  vertices := {
    toFun i := p.getVert i.val
    inj' := by
      intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn' (by change i.val ≤ p.length - 1; omega)
        (by change j.val ≤ p.length - 1; omega) hij }
  specified i := by
    refine ⟨(), ?_⟩
    have hnext : p.getVert (cyclicNext (by have := hp.three_le_length; omega) i).val =
        p.getVert (i.val + 1) := by
      by_cases h : i.val + 1 < p.length
      · simp [cyclicNext, Nat.mod_eq_of_lt h]
      · have he : i.val + 1 = p.length := by omega
        simp [cyclicNext, he]
    change D.edge (p.getVert i.val)
      (p.getVert (cyclicNext (by have := hp.three_le_length; omega) i).val) = some ()
    rw [hnext]
    exact p.adj_getVert_succ i.isLt

/-- A homomorphically feasible Atomic cycle in Age K2 is genuinely
bipartite as a cycle graph. -/
theorem cycleHom_two_bipartite {n : Nat} {D : Diagram onePalette n}
    (C : SimpleCycle D) {B : Model onePalette} (hB : cliqueAge 2 B)
    (h : CycleHomInto C B) : (cycleGraph C.length).IsBipartite := by
  obtain ⟨point, htag, hedge⟩ := h
  let c : Fin C.length → Fin 2 := fun i => Fin.castLE hB (point i)
  have hn (i : Fin C.length) : c i ≠ c (cyclicNext (by have := C.length_ge_three; omega) i) := by
    obtain ⟨a, ha⟩ := C.specified i
    have hne := B.ne_of_edge (hedge i a ha)
    intro he
    apply hne
    dsimp [c] at he
    apply Fin.ext
    exact congrArg (fun z : Fin 2 => z.val) he
  refine ⟨{ toFun := c, map_rel' := ?_ }⟩
  intro i j hij
  rcases cycleGraph_adj_or_next C.length_ge_three hij with h | h
  · subst j; exact hn i
  · subst i; exact (hn j).symm

/-- The exact locally-allowed SemanticCCO interface is discharged for the
actual finite age of K2, using no global-colouring premise. -/
theorem cliqueTwo_semanticCCO : SemanticCCO (cliqueAge 2) := by
  intro n D _allowed cycles
  have hc : CyclesFeasibleTwo (diagramGraph D) := by
    intro x p hp
    let C := walkSimpleCycle D p hp
    obtain ⟨B, hB, hhom⟩ := cycles C
    exact cycleHom_two_bipartite C hB hhom
  obtain ⟨f⟩ := cyclesFeasibleTwo_isBipartite (diagramGraph D) hc
  refine ⟨clique 2, le_rfl, ⟨{ vertex := f, tag_eq := ?_, edge_eq := ?_ }⟩⟩
  · intro x
    change (_ : Unit) = _
    exact Subsingleton.elim _ _
  · intro x y a ha
    cases a
    have hne := f.map_rel' ha
    exact if_neg hne

/-- Missing CCO is witnessed by one complete four-point diagram, despite
actual AP, allowed pairs, genuine small diagrams and feasible cycles. -/
theorem cliqueThree_not_semanticCCO : ¬SemanticCCO (cliqueAge 3) := by
  intro hc
  exact cliqueFour_no_hom (hc (clique 4).diagram
    (localAllowed_of_small _ _ cliqueFour_small) cliqueFour_cycles)

/-- Regard any simple graph as a partial one-atom diagram. -/
def graphDiagram {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Diagram onePalette n where
  tag _ := ()
  edge x y := if G.Adj x y then some () else none
  edge_self x := by simp
  edge_reverse x y := by
    by_cases h : G.Adj x y
    · have h' := h.symm
      simp [h, h', onePalette]
    · have h' : ¬G.Adj y x := fun h' => h h'.symm
      simp [h, h']
  typed _ _ _ _ := ⟨rfl, rfl⟩

/-- Partial induced restriction. Completeness is deliberately not invented. -/
def restrictDiagram {n m : Nat} (D : Diagram onePalette n) (v : Fin m → Fin n) : Diagram onePalette m where
  tag x := D.tag (v x)
  edge x y := D.edge (v x) (v y)
  edge_self x := D.edge_self (v x)
  edge_reverse x y := D.edge_reverse (v x) (v y)
  typed x y a ha := D.typed (v x) (v y) a ha

def fiveCycleDiagram : Diagram onePalette 5 := graphDiagram (cycleGraph 5)

/-- This particular partial input really has locally allowed types and pairs. -/
theorem fiveCycleDiagram_allowed : LocalAllowed (cliqueAge 2) fiveCycleDiagram := by
  constructor
  · intro x; exact ⟨clique 1, by change 1 ≤ 2; omega, ⟨0, by change 0 < 1; omega⟩, rfl⟩
  · intro x y a ha
    cases a
    exact ⟨clique 2, le_rfl, ⟨0, by change 0 < 2; omega⟩, ⟨1, by change 1 < 2; omega⟩, rfl, rfl, rfl⟩

/-- Every three-point partial piece has an actual homomorphism to a K2 age member. -/
theorem fiveCycleDiagram_triples (v : Fin 3 → Fin 5) :
    Nonempty (Hom (restrictDiagram fiveCycleDiagram v) (clique 2)) := by
  obtain ⟨c, hc⟩ := fiveCycle_every_three_colourable v
  refine ⟨{ vertex := c, tag_eq := fun _ => rfl, edge_eq := ?_ }⟩
  intro x y a ha
  cases a
  have hxy : (cycleGraph 5).Adj (v x) (v y) := by
    change (if (cycleGraph 5).Adj (v x) (v y) then some () else none) = some () at ha
    split_ifs at ha with h
    exact h
  exact if_neg (hc x y hxy)

/-- Yet no member of the actual K2 age receives the entire partial five-cycle. -/
theorem fiveCycleDiagram_no_hom :
    ¬∃ B : Model onePalette, cliqueAge 2 B ∧ Nonempty (Hom fiveCycleDiagram B) := by
  rintro ⟨B, hB, ⟨f⟩⟩
  apply fiveCycle_no_two_colouring
  refine ⟨{ toFun := fun x => Fin.castLE hB (f.vertex x), map_rel' := ?_ }⟩
  intro x y hxy heq
  have hE : fiveCycleDiagram.edge x y = some () := by
    change (if (cycleGraph 5).Adj x y then some () else none) = some ()
    exact if_pos hxy
  have hne := B.ne_of_edge (f.edge_eq x y () hE)
  apply hne
  apply Fin.ext
  exact congrArg (fun z : Fin 2 => z.val) heq

/-- The five-cycle is genuinely outside the COMPLETE-input premise. -/
theorem fiveCycleDiagram_incomplete :
    fiveCycleDiagram.edge (0 : Fin 5) (2 : Fin 5) = none := by decide

end CCO.RelationalCompletion.Atomic.Boundaries
