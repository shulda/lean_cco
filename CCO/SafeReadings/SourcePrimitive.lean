import CCO.SafeReadings.TransversalSource
import CCO.SafeReadings.PrimitivePowers

/-! The actual owner-fibre actions induce the canonical Sigma action used
by the accepted source engines. Its agreement with the separately built
whole-U action is proved pointwise; full sort primitivity is then read
from the actual B025 owner/fine-colour automorphism theorem. -/
universe v w t
namespace CCO.SafeReadings.TransversalSource
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open OwnerTransversal
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

/-- The actual full named automorphism group acts on each fixed owner fibre. -/
instance fibreAction (b : ↥B) : MulAction (Motion S H R B) (Carrier S H R B b) where
  smul g x := fibrePerm S H R B (TransversalAge.model S H R B) b g x
  one_smul _x := Subtype.ext rfl
  mul_smul _g _h _x := Subtype.ext rfl

/-- This is explicitly the canonical Sigma action of those component actions. -/
@[instance_reducible] def canonicalSigmaAction : MulAction (Motion S H R B) (Σ b : ↥B, Carrier S H R B b) :=
  @Sigma.instMulAction ↥B (Motion S H R B) (Carrier S H R B) inferInstance
    (fun b => fibreAction S H R B b)

/-- The new canonical action is the SAME actual automorphism on points
as the original whole-U Sigma action, despite its different presentation. -/
theorem canonical_smul_eq (g : Motion S H R B) (p : Σ b : ↥B, Carrier S H R B b) :
    @SMul.smul _ _ (canonicalSigmaAction S H R B).toSMul g p =
      @SMul.smul _ _ (motionAction S H R B).toSMul g p := by
  apply (sigmaEquiv S H R B).injective
  rcases p with ⟨b,x⟩
  change g.val x.val = (sigmaEquiv S H R B) ((sigmaEquiv S H R B).symm (g.val x.val))
  exact ((sigmaEquiv S H R B).apply_symm_apply _).symm

/-- Full tuple homogeneity transferred to the canonical component action
required by ActionBridge, SAP and the accepted selector engines. -/
theorem canonical_homogeneous :
    @HomogeneousSource _ _ (source S H R B) (Motion S H R B) inferInstance
      (canonicalSigmaAction S H R B) := by
  have K := homogeneous S H R B
  refine @HomogeneousSource.mk _ _ _ _ _ (canonicalSigmaAction S H R B) ?_ ?_ ?_
  · intro g p
    exact (congrArg Sigma.fst (canonical_smul_eq S H R B g p)).trans (K.preserves_sort g p)
  · intro g p q
    exact (congrArg₂ (taggedColour (source S H R B))
      (canonical_smul_eq S H R B g p) (canonical_smul_eq S H R B g q)).trans
        (K.preserves_colours g p q)
  · intro V hV f h hc
    obtain ⟨g,hg⟩ := K.extends_finite_diagram f h hc
    exact ⟨g, fun v => (canonical_smul_eq S H R B g (f v)).trans (hg v)⟩

/-- The entire actual owner sort is primitive under its FULL named
owner/fine-colour automorphism group. There is no finite-definability restriction. -/
theorem sortwise_primitive : SortwisePrimitive (source S H R B) := by
  intro b Q hQ
  apply primitive S H R B b Q
  intro g x y hxy
  have hinv := Selectors.invariantSetoid_of_colourInvariant (source S H R B)
    (canonical_homogeneous S H R B) Q hQ
  exact (hinv g x y).mpr hxy

end
end CCO.SafeReadings.TransversalSource
