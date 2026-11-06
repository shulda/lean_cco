import CCO.HiddenSAPReadings.Homogeneity
import CCO.TerminalPowers.FullSource

/-! The global joint lift is induced by ONE genuine FULL original
automorphism. Its real restriction is recovered through the true Id
coordinates; mixed real/quotient same-point pairs then determine its action
on EVERY quotient class. No closure of an arbitrary witness group is used. -/

universe u v w z
namespace CCO.HiddenSAPReadings
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.TerminalPowers
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable (H : HomogeneousSource S (FullAut S))

def realIdCoordinate (i : ι) : OriginalCompletedCoordinateCode S H := ⟨i,.inl ()⟩

/-- The original real sort is literally its quotient by real equality. -/
def realIdQuotientEquiv (i : ι) : X i ≃ CoordinateValue S H (realIdCoordinate S H i) where
  toFun := Quotient.mk (⊥ : ColourEq S i).val
  invFun q := Quotient.liftOn q id (by intro x y h; exact h)
  left_inv _ := rfl
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ x => rfl

/-- The real restriction of the SAME global coordinate family. -/
def coordinateRealEquiv
    (e : ∀ C, CoordinateValue S H C ≃ CoordinateValue S H C) (i : ι) : X i ≃ X i :=
  (realIdQuotientEquiv S H i).trans
    ((e (realIdCoordinate S H i)).trans (realIdQuotientEquiv S H i).symm)

theorem coordinateRealEquiv_quotient
    (e : ∀ C, CoordinateValue S H C ≃ CoordinateValue S H C) (i : ι) (x : X i) :
    Quotient.mk (⊥ : ColourEq S i).val (coordinateRealEquiv S H e i x) =
      e (realIdCoordinate S H i) (Quotient.mk (⊥ : ColourEq S i).val x) :=
  (realIdQuotientEquiv S H i).apply_symm_apply _

/-- Actual pair witnesses produced by the joint lift, on the FULL
original group. This is proved by the source theorem below, not a new
source assumption or a requirement that finite maps already lift. -/
def CoordinatePairs (e : ∀ C, CoordinateValue S H C ≃ CoordinateValue S H C) : Prop :=
  ∀ C D (q : CoordinateValue S H C) (r : CoordinateValue S H D), ∃ g : FullAut S,
    (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H C)).act g q = e C q ∧
    (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H D)).act g r = e D r

theorem coordinateRealEquiv_preserves_colours
    (e : ∀ C, CoordinateValue S H C ≃ CoordinateValue S H C)
    (hPair : CoordinatePairs S H e) (i j : ι) (x : X i) (y : X j) :
    S.colour (coordinateRealEquiv S H e i x) (coordinateRealEquiv S H e j y) = S.colour x y := by
  obtain ⟨g,hgx,hgy⟩ := hPair (realIdCoordinate S H i) (realIdCoordinate S H j)
    (Quotient.mk (⊥ : ColourEq S i).val x) (Quotient.mk (⊥ : ColourEq S j).val y)
  have hx : g • x = coordinateRealEquiv S H e i x :=
    Quotient.exact (hgx.trans (coordinateRealEquiv_quotient S H e i x).symm)
  have hy : g • y = coordinateRealEquiv S H e j y :=
    Quotient.exact (hgy.trans (coordinateRealEquiv_quotient S H e j y).symm)
  rw [← hx,← hy]
  exact fullAut_colour S g i j x y

/-- ONE actual FULL original typed colour automorphism, constructed
from the real restriction rather than postulated as another provider. -/
def coordinateFullOriginal
    (e : ∀ C, CoordinateValue S H C ≃ CoordinateValue S H C)
    (hPair : CoordinatePairs S H e) : FullAut S :=
  ⟨coordinateRealEquiv S H e,coordinateRealEquiv_preserves_colours S H e hPair⟩

/-- The SAME original automorphism induces the lift on ALL classes,
including quotient vertices absent from the displayed finite domain. -/
theorem coordinateFullOriginal_on_every_coordinate
    (e : ∀ C, CoordinateValue S H C ≃ CoordinateValue S H C)
    (hPair : CoordinatePairs S H e)
    (C : OriginalCompletedCoordinateCode S H) (q : CoordinateValue S H C) :
    (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H C)).act
      (coordinateFullOriginal S H e hPair) q = e C q := by
  obtain ⟨x,hx⟩ := Quotient.exists_rep q
  rw [← hx]
  obtain ⟨g,hgx,hgq⟩ := hPair (realIdCoordinate S H C.1) C
    (Quotient.mk (⊥ : ColourEq S C.1).val x)
    (Quotient.mk (originalCompletedCoordinateKernel S H C).val x)
  have hReal : g • x = coordinateRealEquiv S H e C.1 x :=
    Quotient.exact (hgx.trans (coordinateRealEquiv_quotient S H e C.1 x).symm)
  change Quotient.mk (originalCompletedCoordinateKernel S H C).val
    (coordinateRealEquiv S H e C.1 x) = _
  rw [← hReal]
  exact hgq

/-- Global equality with the literal original interpreted action. -/
theorem coordinatePermutation_eq_full_original
    (e : ∀ C, CoordinateValue S H C ≃ CoordinateValue S H C)
    (hPair : CoordinatePairs S H e) (x : OriginalCompletedNamedCarrier S H) :
    coordinatePermutation S H e x =
      originalCompletedNamedAct S H (coordinateFullOriginal S H e hPair) x := by
  obtain ⟨C,q,hq⟩ := original_completed_coordinate_reading_exists S H x
  rw [← reading_vertex S H hq,coordinatePermutation_vertex,
    ← coordinateVertex_equivariant,coordinateFullOriginal_on_every_coordinate]

/-- Unary enrichment keeps this SAME original lift, on the entire
signature, not just on the finite displayed map. -/
theorem coordinateAutomorphism_eq_full_original (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    (e : ∀ C, CoordinateValue S H C ≃ CoordinateValue S H C)
    (hPair : CoordinatePairs S H e) :
    coordinateAutomorphism S H sap nr2 e hPair =
      originalCompletedMotionHom S H sap nr2 (coordinateFullOriginal S H e hPair) := by
  apply Subtype.ext
  apply Equiv.ext
  exact coordinatePermutation_eq_full_original S H e hPair

/-- Source joint lifting: actual FULL original g, no extra lift premise. -/
theorem finite_coordinate_family_full_original_lift [∀ i, Countable (X i)]
    (cco : SemanticCCO.{u,v,max u v,w} S) (nr2 : Selectors.OriginalNR2 S)
    {I : Type z} [Finite I] (sort : I → OriginalCompletedCoordinateCode S H)
    (source target : ∀ a, CoordinateValue S H (sort a))
    (hPairs : ∀ a b, ∃ g : FullAut S,
      (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H (sort a))).act g
        (source a) = target a ∧
      (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H (sort b))).act g
        (source b) = target b) :
    ∃ g : FullAut S, ∀ a,
      (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H (sort a))).act g
        (source a) = target a := by
  obtain ⟨e,hPair,hExt⟩ := finite_coordinate_family_lift S H cco nr2 sort source target hPairs
  exact ⟨coordinateFullOriginal S H e hPair,fun a =>
    (coordinateFullOriginal_on_every_coordinate S H e hPair (sort a) (source a)).trans (hExt a)⟩

/-- Every whole finite closed hidden partial isomorphism, with exactly
its original displayed vertices, extends through ONE FULL original g. -/
theorem closed_embeddings_full_original_lift [∀ i, Countable (X i)]
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (A : (originalCompletedStructure S H sap nr2).Piece)
    (f g : A.Embedding Set.univ) :
    ∃ h : FullAut S, ∀ a, originalCompletedNamedAct S H h (f.point a) = g.point a := by
  let sort : A.points → OriginalCompletedCoordinateCode S H :=
    fun a => ((coordinateEquiv S H).symm (f.point a)).1
  let source : ∀ a, CoordinateValue S H (sort a) :=
    fun a => ((coordinateEquiv S H).symm (f.point a)).2
  have hsort (a : A.points) : originalCompletedVertexSort S H (f.point a) =
      originalCompletedVertexSort S H (g.point a) :=
    congrArg ULift.down ((f.sort_eq a).trans (g.sort_eq a).symm)
  let target : ∀ a, CoordinateValue S H (sort a) :=
    fun a => sameSortValue S H (f.point a) (g.point a) (hsort a)
  have hsource (a : A.points) : coordinateVertex S H (sort a) (source a) = f.point a :=
    (coordinateEquiv S H).apply_symm_apply _
  have htarget (a : A.points) : coordinateVertex S H (sort a) (target a) = g.point a :=
    sameSortValue_vertex S H _ _ _
  have hPairs (a b : A.points) : ∃ h : FullAut S,
      (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H (sort a))).act h
        (source a) = target a ∧
      (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H (sort b))).act h
        (source b) = target b := by
    obtain ⟨h,ha,hb⟩ := closed_embeddings_pair_motion S H sap nr2 A f g a b
    refine ⟨h,?_,?_⟩
    · apply coordinateVertex_injective S H (sort a)
      rw [coordinateVertex_equivariant,hsource,htarget]
      exact ha
    · apply coordinateVertex_injective S H (sort b)
      rw [coordinateVertex_equivariant,hsource,htarget]
      exact hb
  obtain ⟨h,hExt⟩ := finite_coordinate_family_full_original_lift S H cco nr2 sort source target hPairs
  refine ⟨h,?_⟩
  intro a
  rw [← hsource a,← coordinateVertex_equivariant,hExt a,htarget]

/-- The proved one-original-g lift supplies actual hidden homogeneity. -/
theorem hidden_homogeneous_via_full_original [∀ i, Countable (X i)]
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    (originalCompletedStructure S H sap nr2).Homogeneous := by
  intro A f g
  obtain ⟨h,hh⟩ := closed_embeddings_full_original_lift S H sap nr2 cco A f g
  exact ⟨originalCompletedMotionHom S H sap nr2 h,hh⟩

end
end CCO.HiddenSAPReadings
