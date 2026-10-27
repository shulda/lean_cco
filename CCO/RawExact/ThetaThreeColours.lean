import CCO.RawExact.ThetaThree
import CCO.RawExact.Convolution

/-!
# B002 C06/C07: actual three-path length-two RAW theta instance

This proves a nontrivial case of word-profile Helly FROM the existing
semantic homomorphic CCO interface: three genuine two-step diversity
words of one original sort. The finite theta diagram has five vertices,
no diagonal edges and no parallel edges. Every simple cycle misses
one private middle, so pairwise actual word witnesses realize it.
The general C06/C07 family and mixed-sort arbitrary lengths remain OPEN.
-/

universe u v w

namespace CCO.RawExact.ThetaThree

/-- Symmetric labelled edges of K2,3: the two roots are 0,1 and the
private middles are 2,3,4. Missing edges are genuinely unspecified. -/
def labelledEdge {A : Type*} (a b : Fin 3 → A)
    (p q : Fin 5) : Option A :=
  if (p = 0 ∧ q = middle 0) ∨ (q = 0 ∧ p = middle 0) then some (a 0)
  else if (p = 0 ∧ q = middle 1) ∨ (q = 0 ∧ p = middle 1) then some (a 1)
  else if (p = 0 ∧ q = middle 2) ∨ (q = 0 ∧ p = middle 2) then some (a 2)
  else if (p = 1 ∧ q = middle 0) ∨ (q = 1 ∧ p = middle 0) then some (b 0)
  else if (p = 1 ∧ q = middle 1) ∨ (q = 1 ∧ p = middle 1) then some (b 1)
  else if (p = 1 ∧ q = middle 2) ∨ (q = 1 ∧ p = middle 2) then some (b 2)
  else none

theorem labelledEdge_comm {A : Type*} (a b : Fin 3 → A)
    (p q : Fin 5) :
    labelledEdge a b p q = labelledEdge a b q p := by
  fin_cases p <;> fin_cases q <;>
    simp [labelledEdge, middle]

/-- Only the six genuinely specified private edges have atomic labels. -/
theorem adj_of_label {A : Type*} (a b : Fin 3 → A)
    (p q : Fin 5) (c : A)
    (h : labelledEdge a b p q = some c) :
    Adj p q := by
  fin_cases p <;> fin_cases q <;>
    first | decide | (simp [labelledEdge, middle] at h)

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}

/-- A valid REAL typed partial diagram: all five formal vertices have
the one original sort; only diversity colours label its six edges. -/
def diagram (a b : Fin 3 → S.Atom i i) :
    PartialDiagram S (Fin 5) where
  finite_type := inferInstance
  vertexSort := fun _ => i
  edge := fun p q _ => labelledEdge a b p q
  edge_reverse := by
    intro p q _ c
    change labelledEdge a b p q = some c ↔
      labelledEdge a b q p = some (S.conv c)
    rw [labelledEdge_comm a b p q, S.symmetricLoop c]

/-- Two selected paths determine every colour on their induced theta
subgraph; the remaining middle is arbitrary and will be omitted by
the given simple cycle. -/
def pairVal {A : Type*} (x z yt yu : A)
    (t u : Fin 3) (p : Fin 5) : A :=
  if p = 0 then x else if p = 1 then z
  else if p = middle t then yt else if p = middle u then yu else x

def covered (t u : Fin 3) (p : Fin 5) : Prop :=
  p = 0 ∨ p = 1 ∨ p = middle t ∨ p = middle u

/-- For each omitted middle, enumerate the other two distinct paths. -/
def otherTwo (omit : Fin 3) : Fin 3 × Fin 3 :=
  if omit = 0 then (1, 2)
  else if omit = 1 then (0, 2)
  else (0, 1)

theorem otherTwo_ne (omit : Fin 3) :
    (otherTwo omit).1 ≠ (otherTwo omit).2 := by
  fin_cases omit <;> decide

theorem otherTwo_covers (omit : Fin 3) (p : Fin 5)
    (h : p ≠ middle omit) :
    covered (otherTwo omit).1 (otherTwo omit).2 p := by
  fin_cases omit <;> fin_cases p <;> simp_all [covered, otherTwo, middle]

/-- The private path pair really respects EVERY allowed edge, with
orientation checked via genuine symmetric same-sort atomic orbitals.
Only the two paths t,u are used; no information about other paths
is presumed or supplied by an axiom. -/
theorem pairVal_preserves
    (a b : Fin 3 → S.Atom i i)
    (t u : Fin 3) (htu : t ≠ u)
    (x z yt yu : X i)
    (hat : S.atomRel (a t) x yt)
    (hbt : S.atomRel (b t) yt z)
    (hau : S.atomRel (a u) x yu)
    (hbu : S.atomRel (b u) yu z) :
    ∀ p q : Fin 5, covered t u p → covered t u q →
      ∀ c : S.Atom i i, labelledEdge a b p q = some c →
        S.colour (pairVal x z yt yu t u p)
          (pairVal x z yt yu t u q) = some c := by
  have hat' : S.colour x yt = some (a t) := hat
  have hbt' : S.colour yt z = some (b t) := hbt
  have hau' : S.colour x yu = some (a u) := hau
  have hbu' : S.colour yu z = some (b u) := hbu
  have hatRev : S.colour yt x = some (a t) := by
    simpa only [S.symmetricLoop] using (S.colour_swap x yt (a t)).mp hat
  have hbtRev : S.colour z yt = some (b t) := by
    simpa only [S.symmetricLoop] using (S.colour_swap yt z (b t)).mp hbt
  have hauRev : S.colour yu x = some (a u) := by
    simpa only [S.symmetricLoop] using (S.colour_swap x yu (a u)).mp hau
  have hbuRev : S.colour z yu = some (b u) := by
    simpa only [S.symmetricLoop] using (S.colour_swap yu z (b u)).mp hbu
  intro p q hp hq c hc
  fin_cases t <;> fin_cases u <;> fin_cases p <;> fin_cases q <;>
    simp_all [covered, pairVal, middle, labelledEdge]

/-- Genuine C07 instance: if all pairs among THREE two-letter RAW
original-sort profiles have a common actual endpoint pair, then
all three have one common actual endpoint pair. Only the source's
SemanticCCO is required; no SAP, quotient or fake STRONG identity. -/
theorem three_two_step_word_helly
    (a b : Fin 3 → S.Atom i i)
    (cco : SemanticCCO S)
    (hPair : ∀ t u : Fin 3, t ≠ u →
      ∃ x z yt yu : X i,
        S.atomRel (a t) x yt ∧ S.atomRel (b t) yt z ∧
        S.atomRel (a u) x yu ∧ S.atomRel (b u) yu z) :
    ∃ x z : X i, ∀ t : Fin 3,
      ∃ y : X i, S.atomRel (a t) x y ∧ S.atomRel (b t) y z := by
  let D := diagram S a b
  have hCycles : ∀ C : SimpleCycle D, CycleHom C := by
    intro C
    have hAdj : ∀ p : Fin C.length,
        Adj (C.vertices p) (C.vertices (cyclicNext C.length_pos p)) := by
      intro p
      obtain ⟨c, hc⟩ := C.specified p
      change labelledEdge a b (C.vertices p)
        (C.vertices (cyclicNext C.length_pos p)) = some c at hc
      exact adj_of_label a b _ _ c hc
    obtain ⟨om, hom⟩ :=
      every_simple_cycle_omits_middle C.length_ge_three
        C.length_pos C.vertices hAdj
    let t := (otherTwo om).1
    let u := (otherTwo om).2
    obtain ⟨x, z, yt, yu, hat, hbt, hau, hbu⟩ :=
      hPair t u (otherTwo_ne om)
    let v := pairVal x z yt yu t u
    refine ⟨fun p => v (C.vertices p), ?_⟩
    intro p c hc
    change labelledEdge a b (C.vertices p)
      (C.vertices (cyclicNext C.length_pos p)) = some c at hc
    exact pairVal_preserves S a b t u (otherTwo_ne om)
      x z yt yu hat hbt hau hbu
      (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
      (otherTwo_covers om _ (hom p))
      (otherTwo_covers om _ (hom (cyclicNext C.length_pos p)))
      c hc
  obtain ⟨f⟩ := cco (Fin 5) D hCycles
  refine ⟨f.point 0, f.point 1, ?_⟩
  intro t
  refine ⟨f.point (middle t), ?_, ?_⟩
  · have hn : (0 : Fin 5) ≠ middle t := by
      fin_cases t <;> decide
    have hed : D.edge 0 (middle t) hn = some (a t) := by
      fin_cases t <;> simp [D, diagram, labelledEdge, middle]
    exact f.preserves_edge 0 (middle t) hn (a t) hed
  · have hn : (middle t : Fin 5) ≠ 1 := by
      fin_cases t <;> decide
    have hed : D.edge (middle t) 1 hn = some (b t) := by
      fin_cases t <;> simp [D, diagram, labelledEdge, middle]
    exact f.preserves_edge (middle t) 1 hn (b t) hed

end CCO.RawExact.ThetaThree
