import CCO.FullPhaseLift.Full.SourceTransport

/-! Whole finite induced ages, including arbitrary complete higher base
patterns in the binary language, transport through the actual source
isomorphism. Both amalgam legs and exact common-root intersections remain
literal maps. -/

set_option backward.isDefEq.respectTransparency.types false
universe u v w u' v' w'
namespace CCO.FullPhaseLift.Full
noncomputable section
variable {κ : Type u} {Y : κ → Type v} {ι : Type u'} {X : ι → Type v'}
variable {T : AtomicSource.{u,v,w} κ Y} {S : AtomicSource.{u',v',w'} ι X}
namespace SourceIso
variable (e : SourceIso T S)
include e

/-- Image of a finite induced source substructure under the SAME actual
whole-point bijection. -/
def imageInduced (A : FiniteInduced (X := Y)) : FiniteInduced (X := X) where
  vertices := e.whole '' A.vertices
  finite_vertices := A.finite_vertices.image e.whole

def imageEquiv (A : FiniteInduced (X := Y)) :
    A.vertices ≃ (e.imageInduced A).vertices where
  toFun p := ⟨e.whole p.val,⟨p.val,p.property,rfl⟩⟩
  invFun q := ⟨e.whole.symm q.val,by
    obtain ⟨p,hp,hq⟩ := q.property
    rw [← hq,e.whole.symm_apply_apply]
    exact hp⟩
  left_inv p := Subtype.ext (e.whole.symm_apply_apply p.val)
  right_inv q := Subtype.ext (e.whole.apply_symm_apply q.val)

@[simp] theorem imageEquiv_val (A : FiniteInduced (X := Y)) (p : A.vertices) :
    (e.imageEquiv A p).val = e.whole p.val := rfl

@[simp] theorem imageEquiv_symm_val (A : FiniteInduced (X := Y))
    (p : (e.imageInduced A).vertices) :
    e.whole ((e.imageEquiv A).symm p).val = p.val := e.whole.apply_symm_apply p.val

def mapEmbedding {A B : FiniteInduced (X := Y)} (f : InducedEmbedding T A B) :
    InducedEmbedding S (e.imageInduced A) (e.imageInduced B) where
  toEmbedding := (e.imageEquiv A).symm.toEmbedding.trans
    (f.toEmbedding.trans (e.imageEquiv B).toEmbedding)
  preserves_sort p := by
    change (e.whole (f.toEmbedding ((e.imageEquiv A).symm p)).val).1 = p.val.1
    rw [e.whole_sort,f.preserves_sort]
    have h := congrArg Sigma.fst (e.imageEquiv_symm_val A p)
    exact h
  preserves_colours p q := by
    have h := (e.whole_tagged_iff _ _ _ _).mp
      (f.preserves_colours ((e.imageEquiv A).symm p) ((e.imageEquiv A).symm q))
    simpa only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
      e.imageEquiv_val,e.imageEquiv_symm_val] using h

def pullInduced (D : FiniteInduced (X := X)) : FiniteInduced (X := Y) where
  vertices := e.whole.symm '' D.vertices
  finite_vertices := D.finite_vertices.image e.whole.symm

def pullEquiv (D : FiniteInduced (X := X)) : D.vertices ≃ (e.pullInduced D).vertices where
  toFun p := ⟨e.whole.symm p.val,⟨p.val,p.property,rfl⟩⟩
  invFun q := ⟨e.whole q.val,by
    obtain ⟨p,hp,hq⟩ := q.property
    rw [← hq,e.whole.apply_symm_apply]
    exact hp⟩
  left_inv p := Subtype.ext (e.whole.apply_symm_apply p.val)
  right_inv q := Subtype.ext (e.whole.symm_apply_apply q.val)

@[simp] theorem pullEquiv_val (D : FiniteInduced (X := X)) (p : D.vertices) :
    e.whole (e.pullEquiv D p).val = p.val := e.whole.apply_symm_apply p.val

/-- Pull back an amalgam leg while retaining its original domain literally. -/
def pullLeg {A : FiniteInduced (X := Y)} {D : FiniteInduced (X := X)}
    (f : InducedEmbedding S (e.imageInduced A) D) :
    InducedEmbedding T A (e.pullInduced D) where
  toEmbedding := (e.imageEquiv A).toEmbedding.trans
    (f.toEmbedding.trans (e.pullEquiv D).toEmbedding)
  preserves_sort p := by
    apply e.sort.injective
    change e.sort (e.whole.symm (f.toEmbedding (e.imageEquiv A p)).val).1 = e.sort p.val.1
    rw [← e.whole_sort,e.whole.apply_symm_apply]
    exact f.preserves_sort (e.imageEquiv A p)
  preserves_colours p q := by
    apply (e.whole_tagged_iff _ _ _ _).mpr
    have h := f.preserves_colours (e.imageEquiv A p) (e.imageEquiv A q)
    simpa only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
      e.imageEquiv_val,e.pullEquiv_val] using h

/-- Actual full binary-age SAP, with exactly the same root and no extra
intersections, transports through the constructed complete source iso. -/
theorem ageSAP (sap : AgeSAP S) : AgeSAP T := by
  constructor
  intro C A B f g
  obtain ⟨D,l,r,comm,inter⟩ := sap.strong_amalgamate
    (e.imageInduced C) (e.imageInduced A) (e.imageInduced B)
    (e.mapEmbedding f) (e.mapEmbedding g)
  refine ⟨e.pullInduced D,e.pullLeg l,e.pullLeg r,?_,?_⟩
  · intro c
    change e.pullEquiv D (l.toEmbedding (e.imageEquiv A (f.toEmbedding c))) =
      e.pullEquiv D (r.toEmbedding (e.imageEquiv B (g.toEmbedding c)))
    apply congrArg (e.pullEquiv D)
    have h := comm (e.imageEquiv C c)
    simpa only [mapEmbedding,Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using h
  · intro a b hab
    have h : l.toEmbedding (e.imageEquiv A a) = r.toEmbedding (e.imageEquiv B b) :=
      (e.pullEquiv D).injective hab
    obtain ⟨c,hc,hc'⟩ := inter (e.imageEquiv A a) (e.imageEquiv B b) h
    refine ⟨(e.imageEquiv C).symm c,?_,?_⟩
    · apply (e.imageEquiv A).injective
      exact hc
    · apply (e.imageEquiv B).injective
      exact hc'

end SourceIso
end
end CCO.FullPhaseLift.Full
