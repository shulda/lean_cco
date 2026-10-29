import CCO.HKNReservoir.Locality.PositivePrefixes
import CCO.StrongExact.FinLinePath
import Lean.Elab.Tactic.Omega

/-! A cycle is read on its original distinct formal vertices. Its closing
diversity atom is tested against the positive path profile; semantic CCO
is used only after the short/long cycle split for the whole diagram. -/
universe u v w z
namespace CCO.HKNReservoir.Locality
open StrongPC SafeReadings
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z} (D : PartialDiagram S V)

private theorem reindex_specified {I : Type*} (vertices : I → V) {p q r : I}
    (he : q = r) (hpq : vertices p ≠ vertices q) (hpr : vertices p ≠ vertices r) :
    (∃ a, D.edge (vertices p) (vertices q) hpq = some a) ↔
      (∃ a, D.edge (vertices p) (vertices r) hpr = some a) := by
  subst r
  rfl

private theorem reindex_preserves {I : Type*} (vertices : I → V)
    (point : ∀ p, X (D.vertexSort (vertices p))) {p q r : I}
    (he : q = r) (hpq : vertices p ≠ vertices q) (hpr : vertices p ≠ vertices r) :
    (∀ a, D.edge (vertices p) (vertices q) hpq = some a →
      S.colour (point p) (point q) = some a) ↔
    (∀ a, D.edge (vertices p) (vertices r) hpr = some a →
      S.colour (point p) (point r) = some a) := by
  subst r
  rfl

private theorem next_castSucc {m : Nat} (h : 0 < m+1) (p : Fin m) :
    cyclicNext h p.castSucc = p.succ := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt p.succ.isLt

private theorem next_last {m : Nat} (h : 0 < m+1) :
    cyclicNext h (Fin.last m) = 0 := by
  apply Fin.ext
  simp [cyclicNext]

private theorem next_ne (n : Nat) (p : Fin (n+3)) :
    p ≠ cyclicNext (by omega : 0 < n+3) p := by
  intro he
  have hv := congrArg Fin.val he
  change p.val = (p.val+1) % (n+3) at hv
  have hp := p.isLt
  by_cases h : p.val+1 < n+3
  · rw [Nat.mod_eq_of_lt h] at hv
    omega
  · have hn : p.val+1 = n+3 := by omega
    rw [hn,Nat.mod_self] at hv
    omega

private theorem vertices_next_ne (n : Nat) (vertices : Fin (n+3) ↪ V)
    (p : Fin (n+3)) : vertices p ≠ vertices (cyclicNext (by omega : 0 < n+3) p) :=
  fun he => next_ne n p (vertices.injective he)

structure CycleLine (n : Nat) where
  vertices : Fin (n+3) ↪ V
  atoms : ∀ p : Fin (n+2),
    S.Atom (D.vertexSort (vertices p.castSucc)) (D.vertexSort (vertices p.succ))
  edges : ∀ p : Fin (n+2), D.edge (vertices p.castSucc) (vertices p.succ)
    (lineStepPair vertices p).ne = some (atoms p)
  closing : S.Atom (D.vertexSort (vertices 0)) (D.vertexSort (vertices (Fin.last (n+2))))
  closeEdge : D.edge (vertices (Fin.last (n+2))) (vertices 0)
    (lineEndpointPair vertices).ne.symm = some (S.conv closing)

namespace CycleLine
variable {n : Nat} (L : CycleLine S D n)

def toCycle : SimpleCycle D where
  length := n+3
  length_ge_three := by omega
  length_pos := by omega
  vertices := L.vertices
  next_ne := vertices_next_ne n L.vertices
  specified := by
    intro p
    refine Fin.lastCases ?_ (fun q => ?_) p
    · apply (reindex_specified S D L.vertices (next_last (m:=n+2) _) _ _).mpr
      exact ⟨S.conv L.closing,L.closeEdge⟩
    · apply (reindex_specified S D L.vertices (next_castSucc (m:=n+2) _ q) _ _).mpr
      exact ⟨L.atoms q,L.edges q⟩

noncomputable def word : PositiveWord S (D.vertexSort (L.vertices 0))
    (D.vertexSort (L.vertices (Fin.last (n+2)))) :=
  (specifiedLinePath D (n+1) L.vertices L.atoms L.edges).word

end CycleLine

theorem specifiedLinePath_wordLength :
    ∀ (n : Nat) (vertices : Fin (n+2) ↪ V)
      (atoms : ∀ p : Fin (n+1),
        S.Atom (D.vertexSort (vertices p.castSucc)) (D.vertexSort (vertices p.succ)))
      (edges : ∀ p : Fin (n+1), D.edge (vertices p.castSucc) (vertices p.succ)
        (lineStepPair vertices p).ne = some (atoms p)),
      wordLength S (specifiedLinePath D n vertices atoms edges).word = n+1 := by
  intro n
  induction n with
  | zero => intro vertices atoms edges; rfl
  | succ n ih =>
    intro vertices atoms edges
    simp only [specifiedLinePath,SpecifiedPath.word,wordLength]
    exact congrArg (fun k : Nat => k+1) (ih _ _ _)

theorem specifiedLinePath_represented_of_points :
    ∀ (n : Nat) (vertices : Fin (n+2) ↪ V)
      (atoms : ∀ p : Fin (n+1),
        S.Atom (D.vertexSort (vertices p.castSucc)) (D.vertexSort (vertices p.succ)))
      (edges : ∀ p : Fin (n+1), D.edge (vertices p.castSucc) (vertices p.succ)
        (lineStepPair vertices p).ne = some (atoms p))
      (point : ∀ p : Fin (n+2), X (D.vertexSort (vertices p))),
      (∀ p : Fin (n+1), S.colour (point p.castSucc) (point p.succ) = some (atoms p)) →
      PositiveWord.represented S (specifiedLinePath D n vertices atoms edges).word
        (point 0) (point (Fin.last (n+1))) := by
  intro n
  induction n with
  | zero => intro vertices atoms edges point h; exact h 0
  | succ n ih =>
    intro vertices atoms edges point h
    let tailVertices : Fin (n+2) ↪ V :=
      ⟨fun p => vertices p.succ,fun _ _ he => Fin.succ_injective _ (vertices.injective he)⟩
    refine ⟨point 1,h 0,?_⟩
    exact ih tailVertices (fun p => atoms p.succ) (fun p => edges p.succ)
      (fun p => point p.succ) (fun p => h p.succ)

namespace CycleLine
variable {n : Nat} (L : CycleLine S D n)

theorem word_length : wordLength S (L.word S D) = n+2 :=
  specifiedLinePath_wordLength S D (n+1) L.vertices L.atoms L.edges

variable {G : Type*} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

include H sap in
theorem cycleHom_iff_profile : CycleHom (L.toCycle S D) ↔
    L.closing ∈ PositiveWord.profile S (L.word S D) := by
  dsimp only [CycleHom,CycleLine.toCycle]
  constructor
  · rintro ⟨point,hCycle⟩
    have hLetters : ∀ p : Fin (n+2),
        S.colour (point p.castSucc) (point p.succ) = some (L.atoms p) := by
      intro p
      have hp := (reindex_preserves S D L.vertices point (next_castSucc (m:=n+2) _ p)
        _ (lineStepPair L.vertices p).ne).mp (hCycle p.castSucc)
      exact hp (L.atoms p) (L.edges p)
    have hClose : S.colour (point (Fin.last (n+2))) (point 0) = some (S.conv L.closing) := by
      have hp := (reindex_preserves S D L.vertices point (next_last (m:=n+2) _)
        _ (lineEndpointPair L.vertices).ne.symm).mp (hCycle (Fin.last (n+2)))
      exact hp (S.conv L.closing) L.closeEdge
    apply (StrongExact.positive_profile_iff_represented S H sap (L.word S D) L.closing).mpr
    refine ⟨point 0,point (Fin.last (n+2)),?_,?_⟩
    · exact specifiedLinePath_represented_of_points S D (n+1) L.vertices L.atoms L.edges point hLetters
    · simpa only [S.conv_invol] using
        (S.colour_swap (point (Fin.last (n+2))) (point 0) (S.conv L.closing)).mp hClose
  · intro hProfile
    obtain ⟨point,hLetters,hClose⟩ := specifiedLine_realizable_of_profile D H sap
      (n+1) L.vertices L.atoms L.edges L.closing hProfile
    refine ⟨point,?_⟩
    intro p
    refine Fin.lastCases ?_ (fun q => ?_) p
    · apply (reindex_preserves S D L.vertices point (next_last (m:=n+2) _)
        _ (lineEndpointPair L.vertices).ne.symm).mpr
      intro a ha
      have he : a = S.conv L.closing := Option.some.inj (ha.symm.trans L.closeEdge)
      subst a
      exact (S.colour_swap _ _ L.closing).mp hClose
    · apply (reindex_preserves S D L.vertices point (next_castSucc (m:=n+2) _ q)
        _ (lineStepPair L.vertices q).ne).mpr
      intro a ha
      have he : a = L.atoms q := Option.some.inj (ha.symm.trans (L.edges q))
      subst a
      exact hLetters q

end CycleLine

theorem cycle_has_line (C : SimpleCycle D) :
    ∃ (n : Nat) (L : CycleLine S D n), L.toCycle S D = C := by
  classical
  rcases C with ⟨m,hThree,hPositive,vertices,nextNe,specified⟩
  obtain ⟨n,rfl⟩ : ∃ n, m = n+3 := ⟨m-3,by omega⟩
  have edges : ∀ p : Fin (n+2), ∃ a,
      D.edge (vertices p.castSucc) (vertices p.succ) (lineStepPair vertices p).ne = some a := by
    intro p
    exact (reindex_specified S D vertices (next_castSucc (m:=n+2) hPositive p)
      (nextNe p.castSucc) (lineStepPair vertices p).ne).mp (specified p.castSucc)
  have closing : ∃ a, D.edge (vertices (Fin.last (n+2))) (vertices 0)
      (lineEndpointPair vertices).ne.symm = some a := by
    exact (reindex_specified S D vertices (next_last (m:=n+2) hPositive)
      (nextNe (Fin.last (n+2))) (lineEndpointPair vertices).ne.symm).mp
        (specified (Fin.last (n+2)))
  let L : CycleLine S D n := {
    vertices := vertices
    atoms := fun p => Classical.choose (edges p)
    edges := fun p => Classical.choose_spec (edges p)
    closing := S.conv (Classical.choose closing)
    closeEdge := by simpa only [S.conv_invol] using Classical.choose_spec closing }
  exact ⟨n,L,rfl⟩

variable {G : Type*} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (primitive : SortwisePrimitive S)

include H sap primitive in
theorem long_cycle_hom (D : PartialDiagram S V) (C : SimpleCycle D)
    (hLength : cycleBound S < C.length) : CycleHom C := by
  obtain ⟨n,L,rfl⟩ := cycle_has_line S D C
  apply (L.cycleHom_iff_profile S D H sap).mpr
  have hFull := profile_full_of_length_gt S H sap primitive (L.word S D) (by
    rw [L.word_length S D]
    have hm : localityBound S+1 ≤ cycleBound S := Nat.le_max_right _ _
    change cycleBound S < n+3 at hLength
    omega)
  rw [hFull]
  trivial

include H sap primitive in
theorem completion_of_short_cycles (cco : SemanticCCO.{u,v,z,w} S) (D : PartialDiagram S V)
    (short : ∀ C : SimpleCycle D, C.length ≤ cycleBound S → CycleHom C) :
    Nonempty (DiagramHom D) := by
  apply cco V D
  intro C
  by_cases h : C.length ≤ cycleBound S
  · exact short C h
  · exact long_cycle_hom S H sap primitive D C (by omega)

end CCO.HKNReservoir.Locality
