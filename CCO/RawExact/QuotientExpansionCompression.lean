import CCO.RawExact.QuotientExpansionCyclePaths
import CCO.RawExact.QuotientExpansionDiagram
import CCO.RawExact.CyclicSuppression
import Mathlib.Tactic.FinCases

/-!
# Compressing actual raw quotient cycles to their marked edge cycle

During compression a segment may jump over deleted positions of one
private word. Its marked-edge identifier is retained, so suppression
preserves every used marked edge as well as all marked vertices.
-/

universe u v w
namespace CCO.RawExact.QuotientExpansion

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {n : Nat} (sort : Fin n → ι) (P : Menus S sort)

/-- A possibly shortened segment of ONE original private word path. -/
def Piece (e : Edge n) (v w : Vertex S sort P) : Prop :=
  ∃ (o : Occurrence S sort P) (p q : PathPosition S (word S sort P o)),
    o.1 = e ∧ p ≠ q ∧ v = atPosition S sort P o p ∧ w = atPosition S sort P o q

def IsMarked (v : Vertex S sort P) : Prop := ∃ m, v = mark S sort P m

theorem piece_contractible_private
    (o : Occurrence S sort P) (p : Interior S sort P o)
    (e f : Edge n) (a b : Vertex S sort P)
    (he : Piece S sort P e a (interior S sort P o p))
    (hf : Piece S sort P f (interior S sort P o p) b)
    (hab : a ≠ b) : e = f ∧ Piece S sort P e a b := by
  obtain ⟨o₁, p₁, q₁, he, _, ha, hp₁⟩ := he
  obtain ⟨o₂, p₂, q₂, hf, _, hp₂, hb⟩ := hf
  have h₁ := interior_occurrence_unique S sort P o o₁ p q₁ hp₁
  have h₂ := interior_occurrence_unique S sort P o o₂ p p₂ hp₂
  subst o₁
  subst o₂
  refine ⟨he.symm.trans hf, o, p₁, q₂, he, ?_, ha, hb⟩
  intro h
  exact hab (ha.trans ((congrArg (atPosition S sort P o) h).trans hb.symm))

theorem piece_contractible
    (v : Vertex S sort P) (hPrivate : ¬ IsMarked S sort P v)
    (e f : Edge n) (a b : Vertex S sort P)
    (he : Piece S sort P e a v) (hf : Piece S sort P f v b) (hab : a ≠ b) :
    e = f ∧ Piece S sort P e a b := by
  cases v with
  | inl m => exact False.elim (hPrivate ⟨m, rfl⟩)
  | inr op => exact piece_contractible_private S sort P op.1 op.2 e f a b he hf hab

/-- A shortened segment between marked vertices retains the original pair. -/
theorem piece_between_marks (e : Edge n) (m r : Fin n)
    (h : Piece S sort P e (mark S sort P m) (mark S sort P r)) :
    (m = left e ∧ r = right e) ∨ (m = right e ∧ r = left e) := by
  obtain ⟨o, p, q, he, hpq, hm, hr⟩ := h
  rw [← he]
  rcases mark_position_endpoint S sort P o p m hm with hp | hp <;>
    rcases mark_position_endpoint S sort P o q r hr with hq | hq
  · exact False.elim (hpq (Fin.ext (hp.1.trans hq.1.symm)))
  · exact Or.inl ⟨hp.2, hq.2⟩
  · exact Or.inr ⟨hp.2, hq.2⟩
  · exact False.elim (hpq (Fin.ext (hp.1.trans hq.1.symm)))

variable (hNonempty : ∀ e, TRel.Nonempty (evaluate S (P e)))

noncomputable def cycleOccurrence (C : SimpleCycle (diagram S sort P hNonempty))
    (k : Fin C.length) : Occurrence S sort P :=
  (simpleCycle_adjacent S sort P hNonempty C k).choose

theorem cycleOccurrence_spec (C : SimpleCycle (diagram S sort P hNonempty))
    (k : Fin C.length) :
    ∃ p q : PathPosition S (word S sort P (cycleOccurrence S sort P hNonempty C k)),
      pathAdjacent S (word S sort P (cycleOccurrence S sort P hNonempty C k)) p q ∧
      C.vertices k = atPosition S sort P (cycleOccurrence S sort P hNonempty C k) p ∧
      C.vertices (cyclicNext C.length_pos k) =
        atPosition S sort P (cycleOccurrence S sort P hNonempty C k) q :=
  (simpleCycle_adjacent S sort P hNonempty C k).choose_spec

/-- The original raw cycle with its literal marked-edge identifiers. -/
noncomputable def initialCycle (C : SimpleCycle (diagram S sort P hNonempty)) :
    CyclicSuppression.LabelledCycle (Piece S sort P) where
  length := C.length
  length_ge_three := C.length_ge_three
  length_pos := C.length_pos
  vertices := C.vertices
  label := fun k => (cycleOccurrence S sort P hNonempty C k).1
  realises := by
    intro k
    obtain ⟨p, q, hpq, hv, hw⟩ := cycleOccurrence_spec S sort P hNonempty C k
    exact ⟨cycleOccurrence S sort P hNonempty C k, p, q, rfl,
      pathAdjacent_ne S _ p q hpq, hv, hw⟩

/-- A compressed actual marked cycle, retaining every original used edge. -/
structure MarkedProjection (C : SimpleCycle (diagram S sort P hNonempty)) where
  length : Nat
  length_ge_three : 3 ≤ length
  length_pos : 0 < length
  vertices : Fin length ↪ Fin n
  edges : Fin length → Edge n
  endpoints : ∀ k,
    (vertices k = left (edges k) ∧ vertices (cyclicNext length_pos k) = right (edges k)) ∨
      (vertices k = right (edges k) ∧ vertices (cyclicNext length_pos k) = left (edges k))
  marked_iff : ∀ m, CycleVertex C (mark S sort P m) ↔ ∃ k, vertices k = m
  labels_iff : ∀ e, CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) e ↔
    ∃ k, edges k = e

/-- Three marked vertices give a genuine simple marked cycle; every
original raw edge identifier appears in this projected cycle. -/
theorem marked_projection_of_three
    (C : SimpleCycle (diagram S sort P hNonempty))
    (hThree : CyclicSuppression.ThreeMarked (initialCycle S sort P hNonempty C) (IsMarked S sort P)) :
    Nonempty (MarkedProjection S sort P hNonempty C) := by
  classical
  obtain ⟨B, hMarked, hVertices, hLabels⟩ := CyclicSuppression.compress_marked
    (IsMarked S sort P) (piece_contractible S sort P)
    (initialCycle S sort P hNonempty C) hThree
  let vertex : Fin B.length → Fin n := fun k => (hMarked k).choose
  have hVertex : ∀ k, B.vertices k = mark S sort P (vertex k) := fun k => (hMarked k).choose_spec
  have hInjective : Function.Injective vertex := by
    intro p q hpq
    apply B.vertices.injective
    exact (hVertex p).trans ((congrArg (mark S sort P) hpq).trans (hVertex q).symm)
  refine ⟨⟨B.length, B.length_ge_three, B.length_pos, ⟨vertex, hInjective⟩, B.label, ?_, ?_, ?_⟩⟩
  · intro k
    have h := B.realises k
    rw [hVertex k, hVertex (cyclicNext B.length_pos k)] at h
    exact piece_between_marks S sort P (B.label k) (vertex k) (vertex (cyclicNext B.length_pos k)) h
  · intro m
    have hMembership := hVertices (mark S sort P m) ⟨m, rfl⟩
    constructor
    · intro hOn
      obtain ⟨k, hk⟩ := hMembership.mpr hOn
      exact ⟨k, Sum.inl.inj ((hVertex k).symm.trans hk)⟩
    · rintro ⟨k, hk⟩
      apply hMembership.mp
      exact ⟨k, (hVertex k).trans (congrArg (mark S sort P) hk)⟩
  · intro e
    exact (hLabels e).symm

end CCO.RawExact.QuotientExpansion
