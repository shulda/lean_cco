import CCO.UnfilteredEP.CoreRetract
import CCO.UnfilteredEP.TemplateAge

/-! B064 C107: restriction to the actual image of a finite-template
retraction preserves reduct-surjectivity and reasonableness along the
SAME prescribed old embedding. No induced-substructure closure of a
functional Ramsey provider is asserted here; C108 has its separate gate. -/

universe u v w z p
namespace CCO.UnfilteredEP.FiniteAge
variable {OldSort : Type u} {Atom : Type v} {Label : Type p}
variable (K : FiniteAge.{u,v,w,z} OldSort Atom) (T : FiniteTemplate OldSort Atom Label)

/-- Every prescribed old induced embedding lifts while preserving the
entire marking already specified on its source. -/
def Reasonable : Prop :=
  ∀ {A B : K.Obj} (f : K.Embedding A B) (a : K.Marking T A),
    ∃ b : K.Marking T B, ∀ x, b.label (f.toFun x) = a.label x

/-- Forget only membership proofs of the retained labels. -/
def includeMarking {U : Set Label} {A : K.Obj}
    (a : K.Marking (T.induced U) A) : K.Marking T A where
  label x := (a.label x).val
  sorted := a.sorted
  pairs := a.pairs

/-- Postcomposition with the actual endomorphism lands in its image. -/
def retractMarking (e : Label → Label) (he : T.Endomorphism e)
    {A : K.Obj} (a : K.Marking T A) : K.Marking (T.induced (Set.range e)) A where
  label x := ⟨e (a.label x),a.label x,rfl⟩
  sorted x := (he.1 (a.label x)).trans (a.sorted x)
  pairs x y r h := he.2 r _ _ (a.pairs x y r h)

/-- An idempotent fixes every actual point of its image. -/
theorem retract_fixes_image (e : Label → Label) (idem : ∀ x, e (e x) = e x)
    (y : Set.range e) : e y.val = y.val := by
  obtain ⟨x,hx⟩ := y.property
  rw [← hx]
  exact idem x

/-- The retained-label marking is preserved literally. -/
@[simp] theorem retract_include_marking (e : Label → Label)
    (he : T.Endomorphism e) (idem : ∀ x, e (e x) = e x)
    {A : K.Obj} (a : K.Marking (T.induced (Set.range e)) A) (x : K.Point A) :
    (K.retractMarking T e he (K.includeMarking T a)).label x = a.label x := by
  apply Subtype.ext
  exact retract_fixes_image e idem (a.label x)

/-- C107 reduct-surjectivity needs only endomorphism preservation. -/
theorem reductSurjective_retract (e : Label → Label) (he : T.Endomorphism e)
    (surjective : K.ReductSurjective T) :
    K.ReductSurjective (T.induced (Set.range e)) := by
  intro A
  obtain ⟨a⟩ := surjective A
  exact ⟨K.retractMarking T e he a⟩

/-- C107 reasonableness: first extend, then retract. Idempotence keeps
every already specified retained label, along the SAME old map. -/
theorem reasonable_retract (e : Label → Label) (he : T.Endomorphism e)
    (idem : ∀ x, e (e x) = e x) (reasonable : K.Reasonable T) :
    K.Reasonable (T.induced (Set.range e)) := by
  intro A B f a
  obtain ⟨b,hb⟩ := reasonable f (K.includeMarking T a)
  refine ⟨K.retractMarking T e he b,?_⟩
  intro x
  apply Subtype.ext
  change e (b.label (f.toFun x)) = (a.label x).val
  rw [hb]
  exact retract_fixes_image e idem (a.label x)

end CCO.UnfilteredEP.FiniteAge
