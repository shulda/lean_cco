import CCO.UnfilteredEP.CoreRestrictedMarkings
import CCO.UnfilteredEP.FiniteCoreCriterion

/-! B064 C108–C109: the optional RELATIONAL core restriction.
The explicit closure gate is the universal property of the actual induced
provider subobject on retained-label vertices. It is automatic for a
hereditary relational provider; a functional provider must supply genuine
closedness. The proof restricts Ramsey/JEP witnesses in that same provider.
It does not assume expansion property or change the genuine main recipe. -/

universe u v w z p q
namespace CCO.UnfilteredEP.FiniteAge.RamseyProvider
variable {OldSort : Type u} {Atom : Type v} {Label : Type p}
variable {K : FiniteAge.{u,v,w,z} OldSort Atom}
variable {T : FiniteTemplate OldSort Atom Label}
variable (P : K.RamseyProvider.{u,v,w,z,p,q} T) (U : Set Label)

def Retained (A : P.Obj) : Prop := ∀ x, (P.marking A).label x ∈ U

/-- A08: the actual induced restriction, with all permitted embeddings
factoring on their SAME old vertex maps. An arbitrary objectwise choice
of smaller host would not meet this gate. -/
structure InducedLabelRestriction where
  object : P.Obj → P.Obj
  retained : ∀ A, P.Retained U (object A)
  inclusion : ∀ A, P.Embedding (object A) A
  factor : ∀ {A B : P.Obj} (f : P.Embedding A B), P.Retained U A →
    ∃ g : P.Embedding A (object B),
      ∀ x, (inclusion B).val.old.toFun (g.val.old.toFun x) = f.val.old.toFun x

/-- The hereditary provider on exactly the retained labels. Its
relations and original vertex maps are unchanged. -/
def retainedProvider : K.RamseyProvider (T.induced U) where
  Obj := {A : P.Obj // P.Retained U A}
  old A := P.old A.val
  marking A := {
    label x := ⟨(P.marking A.val).label x,A.property x⟩
    sorted := (P.marking A.val).sorted
    pairs := (P.marking A.val).pairs }
  allowed A B f := P.allowed A.val B.val {
    old := f.old
    labels x := congrArg Subtype.val (f.labels x) }
  id_allowed A := P.id_allowed A.val
  comp_allowed _g _f hg hf := P.comp_allowed _ _ hg hf

variable {P U}

def forgetRetained {A B : (P.retainedProvider U).Obj}
    (f : (P.retainedProvider U).Embedding A B) : P.Embedding A.val B.val :=
  ⟨⟨f.val.old,fun x => congrArg Subtype.val (f.val.labels x)⟩,f.property⟩

def liftRetained {A B : (P.retainedProvider U).Obj}
    (f : P.Embedding A.val B.val) : (P.retainedProvider U).Embedding A B :=
  ⟨⟨f.val.old,fun x => Subtype.ext (f.val.labels x)⟩,f.property⟩

theorem liftRetained_comp {A B C : (P.retainedProvider U).Obj}
    (g : P.Embedding B.val C.val) (f : P.Embedding A.val B.val) :
    (liftRetained g).comp (liftRetained f) = liftRetained (g.comp f) := by
  apply Embedding.ext
  rfl

variable (P U)

/-- Every legal retained marking has a whole actual retained provider
expansion: the original reduct-surjective lift is onto on old points. -/
theorem retained_redSurjective (lift : P.ReductSurjective) :
    (P.retainedProvider U).ReductSurjective := by
  intro A a
  obtain ⟨D,e,onto⟩ := lift A (K.includeMarking T a)
  have hd : P.Retained U D := by
    intro y
    obtain ⟨x,rfl⟩ := onto y
    rw [e.labels x]
    exact (a.label x).property
  refine ⟨⟨D,hd⟩,⟨e.old,?_⟩,onto⟩
  intro x
  exact Subtype.ext (e.labels x)

/-- The SAME actual singleton shapes survive induced label restriction. -/
def retained_singletons (S : P.Singletons) : (P.retainedProvider U).Singletons where
  object t := ⟨S.object t.val,fun x => by
    rw [S.only_point t.val x,S.labelled]
    exact t.property⟩
  point t := S.point t.val
  only_point t := S.only_point t.val
  labelled t := Subtype.ext (S.labelled t.val)
  at_vertex A x := by
    obtain ⟨f,hf⟩ := S.at_vertex A.val x
    exact ⟨liftRetained f,hf⟩

/-- JEP witnesses are restricted to the retained induced subobject. -/
theorem retained_JEP (R : P.InducedLabelRestriction U) (jep : P.JEP) :
    (P.retainedProvider U).JEP := by
  intro A B
  obtain ⟨D,⟨a⟩,⟨b⟩⟩ := jep A.val B.val
  obtain ⟨a',_⟩ := R.factor a A.property
  obtain ⟨b',_⟩ := R.factor b B.property
  exact ⟨⟨R.object D,R.retained D⟩,⟨liftRetained a'⟩,⟨liftRetained b'⟩⟩

/-- Every map from a retained source lands in the induced restriction.
Hence an original Ramsey arrow restricts to a retained Ramsey arrow. -/
theorem retained_Ramsey (R : P.InducedLabelRestriction U) (ramsey : P.Ramsey) :
    (P.retainedProvider U).Ramsey := by
  classical
  intro A B n hn
  obtain ⟨C,hC⟩ := ramsey A.val B.val n hn
  let C' : (P.retainedProvider U).Obj := ⟨R.object C,R.retained C⟩
  refine ⟨C',?_⟩
  intro colour
  let factor (f : P.Embedding A.val C) : P.Embedding A.val (R.object C) :=
    (R.factor f A.property).choose
  have factor_law (f : P.Embedding A.val C) :
      (R.inclusion C).comp (factor f) = f := by
    apply Embedding.ext
    funext x
    exact (R.factor f A.property).choose_spec x
  let oldColour (f : P.Embedding A.val C) : Fin n := colour (liftRetained (factor f))
  obtain ⟨g,hg⟩ := hC oldColour
  obtain ⟨g',hgp⟩ := R.factor g B.property
  have glaw : (R.inclusion C).comp g' = g := by
    apply Embedding.ext
    funext x
    exact hgp x
  refine ⟨liftRetained g',?_⟩
  intro f h
  have same (a : (P.retainedProvider U).Embedding A B) :
      factor (g.comp (forgetRetained a)) = g'.comp (forgetRetained a) := by
    apply Embedding.ext
    funext x
    apply (R.inclusion C).val.old.injective
    have hl := congrArg
      (fun e : P.Embedding A.val C => e.val.old.toFun x)
      (factor_law (g.comp (forgetRetained a)))
    change (R.inclusion C).val.old.toFun
        ((factor (g.comp (forgetRetained a))).val.old.toFun x) = _ at hl
    have hr := congrArg
      (fun e : P.Embedding B.val C => e.val.old.toFun ((forgetRetained a).val.old.toFun x))
      glaw
    exact hl.trans hr.symm
  have hm := hg (forgetRetained f) (forgetRetained h)
  change colour (liftRetained (factor (g.comp (forgetRetained f)))) =
    colour (liftRetained (factor (g.comp (forgetRetained h)))) at hm
  rw [same,same] at hm
  have hf : liftRetained (forgetRetained f) = f := by apply Embedding.ext; rfl
  have hh : liftRetained (forgetRetained h) = h := by apply Embedding.ext; rfl
  simpa only [← liftRetained_comp,hf,hh] using hm

end CCO.UnfilteredEP.FiniteAge.RamseyProvider

namespace CCO.UnfilteredEP.FiniteAge
variable {OldSort : Type u} {Atom : Type v} {Label : Type p}
variable (K : FiniteAge.{u,v,w,z} OldSort Atom) (T : FiniteTemplate OldSort Atom Label)

/-- Actual pair witnesses remain actual, even with repeated labels:
postcompose their entire marking with the retraction fixing both ends. -/
theorem retract_allPairsRealized (e : Label → Label) (he : T.Endomorphism e)
    (idem : ∀ x, e (e x) = e x) (pairs : K.AllPairsRealized T) :
    K.AllPairsRealized (T.induced (Set.range e)) := by
  intro r s t h
  obtain ⟨A,a,x,y,hxy,hcol,hx,hy⟩ := pairs r s.val t.val h
  refine ⟨A,K.retractMarking T e he a,x,y,hxy,hcol,?_,?_⟩
  · apply Subtype.ext
    change e (a.label x) = s.val
    rw [hx]
    exact retract_fixes_image e idem s
  · apply Subtype.ext
    change e (a.label y) = t.val
    rw [hy]
    exact retract_fixes_image e idem t

/-- C109: optional retained-label EP follows from the independently
proved finite criterion and the actual relational/closed restriction. -/
theorem minimum_core_retract_EP [Finite Label] [Finite Atom]
    (P : K.RamseyProvider.{u,v,w,z,p,q} T)
    (S : P.Singletons) (_surjective : K.ReductSurjective T)
    (lift : P.ReductSurjective) (jep : P.JEP) (ramsey : P.Ramsey)
    (pairs : K.AllPairsRealized T)
    (e : Label → Label) (he : T.Endomorphism e) (idem : ∀ x, e (e x) = e x)
    (minimal : ∀ f, T.Endomorphism f → T.rank e ≤ T.rank f)
    (closed : P.InducedLabelRestriction (Set.range e)) :
    K.UnaryEP (T.induced (Set.range e)) := by
  apply (P.retainedProvider (Set.range e)).unary_EP_of_finite_template_core
    (P.retained_singletons (Set.range e) S)
    (P.retained_redSurjective (Set.range e) lift)
    (P.retained_JEP (Set.range e) closed jep)
    (P.retained_Ramsey (Set.range e) closed ramsey)
    (K.retract_allPairsRealized T e he idem pairs)
  exact T.minimum_rank_retract_image_core e he idem minimal

end CCO.UnfilteredEP.FiniteAge
