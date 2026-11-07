import CCO.GuardedOldSeams.LiftOrdered

/-! The reconstructed target can be chosen finite and unary closed in
the actual completed source. Global HE is not global injectivity. -/

universe u v w r z
namespace CCO.GuardedOldSeams
open CCO.UnarySupport CCO.UnarySupport.Structure

section Partial
variable {L : Signature.{u}} {P : Type v} {Q : Type w}
variable {C : Structure L P} {A : Structure L Q}

theorem total_hom_range_closed (f : Hom C A) (hC : C.Total) :
    A.IsClosed (Set.range f.point) := by
  rintro U _ ⟨p,rfl⟩ y hy
  have hs : C.sort p = L.input U :=
    (f.sort_eq p).symm.trans (A.func_sorted U (f.point p) y hy).1
  obtain ⟨q,hq⟩ := hC U p hs
  exact ⟨q,A.functional U (f.point p) (f.point q) y (f.map_func U p q hq) hy⟩

def rangeHom (f : Hom C A) (hC : C.Total) :
    Hom C (A.induce (Set.range f.point) (total_hom_range_closed f hC)) where
  point p := ⟨f.point p,Set.mem_range_self p⟩
  sort_eq p := f.sort_eq p
  map_func U p q h := f.map_func U p q h
  map_rel R xs h := f.map_rel R xs h

theorem rangeHom_HE (f : Hom C A) (hC : C.Total) (hf : f.HomEmbedding) :
    (rangeHom f hC).HomEmbedding := by
  intro D hD hirr
  have he := hf D hD hirr
  refine ⟨?_,?_,?_⟩
  · intro p hp q hq hpq
    exact he.1 hp hq (congrArg Subtype.val hpq)
  · intro R xs hxs
    exact he.2.1 R xs hxs
  · intro U p hp y hy
    obtain ⟨q,hq,hU,hqy⟩ := he.2.2 U p hp y.val hy
    exact ⟨q,hq,hU,Subtype.ext hqy⟩

/-- A finite source with a total unary diagram has a finite actual
closed image; induced HE survives passage to that exact image. -/
theorem finite_closed_HE_image [Finite P]
    (f : Hom C A) (hC : C.Total) (hf : f.HomEmbedding) :
    ∃ D : Set Q, D.Finite ∧ ∃ hD : A.IsClosed D,
      ∃ g : Hom C (A.induce D hD), g.HomEmbedding := by
  exact ⟨Set.range f.point,Set.finite_range _,total_hom_range_closed f hC,
    rangeHom f hC,rangeHom_HE f hC hf⟩

def closedInducedHom {D : Set Q} (hD : A.IsClosed D)
    (f : Hom C (A.induce D hD)) : Hom C A where
  point p := (f.point p).val
  sort_eq p := f.sort_eq p
  map_func U p q h := f.map_func U p q h
  map_rel R xs h := f.map_rel R xs h

theorem closedInducedHom_HE {D : Set Q} (hD : A.IsClosed D)
    (f : Hom C (A.induce D hD)) (hf : f.HomEmbedding) :
    (closedInducedHom hD f).HomEmbedding := by
  intro B hB hirr
  have he := hf B hB hirr
  refine ⟨?_,?_,?_⟩
  · intro p hp q hq hpq
    exact he.1 hp hq (Subtype.ext hpq)
  · intro R xs hxs
    exact he.2.1 R xs hxs
  · intro U p hp y hy
    have hyD : y ∈ D := hD U (f.point p).val (f.point p).property hy
    obtain ⟨q,hq,hU,hqy⟩ := he.2.2 U p hp ⟨y,hyD⟩ hy
    exact ⟨q,hq,hU,congrArg Subtype.val hqy⟩

end Partial

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings CCO.GuardedTwoRoot
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
variable (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
variable (tests : BoundedJoinedPairTests S H sap nr2 F)

/-- Source completion means a finite induced unary-closed piece of
the actual MI-only target, not a hypothetical completion class. -/
def FiniteHiddenCompletion : Prop :=
  ∃ D : Set (OriginalCompletedNamedCarrier S H), D.Finite ∧
    ∃ hD : (originalPartialTarget S H sap nr2).IsClosed D,
      ∃ f : Hom F ((originalPartialTarget S H sap nr2).induce D hD), f.HomEmbedding

theorem OrderedRootRealization.finiteHiddenCompletion
    (R : OrderedRootRealization S H sap nr2 F hUnary tests) :
    FiniteHiddenCompletion S H sap nr2 F :=
  finite_closed_HE_image R.hiddenHom
    (total_of_unary_admissible hUnary (originalPartialTarget_total S H sap nr2))
    R.hiddenHom_HE

include hUnary in
theorem finite_hidden_completion_iff :
    FiniteHiddenCompletion S H sap nr2 F ↔
      ∃ f : Hom F (originalPartialTarget S H sap nr2), f.HomEmbedding := by
  constructor
  · rintro ⟨D,_,hD,f,hf⟩
    exact ⟨closedInducedHom hD f,closedInducedHom_HE hD f hf⟩
  · rintro ⟨f,hf⟩
    exact finite_closed_HE_image f
      (total_of_unary_admissible hUnary (originalPartialTarget_total S H sap nr2)) hf

theorem ordered_roots_iff_finite_hidden_completion :
    Nonempty (OrderedRootRealization S H sap nr2 F hUnary tests) ↔
      FiniteHiddenCompletion S H sap nr2 F := by
  rw [ordered_roots_iff_hidden_HE]
  exact (finite_hidden_completion_iff S H sap nr2 F hUnary).symm

end CCO.GuardedOldSeams
