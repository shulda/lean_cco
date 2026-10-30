import CCO.RankInduction.Basis
import CCO.RankInduction.FactorWitnessTransport

/-! The actual relative constructor gives a plain rooted witness and a
separate closed choice on its SAME real carrier. Ordinary extensions are
derived from genuine coarse EPPA plus all prescribed source requests. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open RawExact ExactCRT Owners.Product Owners.Provider
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization AclOwners RelativeMI

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M] [DecidableEq M] [Infinite M]
variable (H : HomogeneousSource S G) (J : ColourEq S ())
variable (A0 : Finset M) (B : Finset (Coarse S H J))
variable (overA0 : ∀ a : ↥A0, coarseOwner S H J a.val ∈ B)
variable {safe : Set (S.Atom () ())}
variable (W : OriginalWitness S H J A0 B overA0 safe)
local instance relativeReadoutCoarseAction : MulAction G (Coarse S H J) := originalQuotientAction S H J

omit [Countable M] [DecidableEq M] [Infinite M] in
theorem relative_ordinary (ep : CoarseEPPAFor S H J A0 B) :
    EPPAFor (G := G) (ι := (Subtype.val : W.carrier → M)) {x | x.val ∈ A0} := by
  let Q := factorQuotient S H J A0 B overA0 W
  intro p dom ran
  have ownerDom : (Q.projectedPartial p).domain ⊆ {b | b.val ∈ coarseOwner S H J '' (↑A0 : Set M)} := by
    rintro b ⟨x, hx, rfl⟩
    exact ⟨x.val, dom hx, rfl⟩
  have ownerRan : ∀ b : (Q.projectedPartial p).domain,
      (Q.projectedPartial p).map b ∈ {b | b.val ∈ coarseOwner S H J '' (↑A0 : Set M)} := by
    intro b
    exact ⟨(p.map (Q.domainLift p b)).val, ran _, rfl⟩
  obtain ⟨γ, extend⟩ := ep (Q.projectedPartial p) ownerDom ownerRan
  have compatible (x : p.domain) : Q.projection (p.map x) = γ.val (Q.projection x.val) := by
    have h := extend ⟨Q.projection x.val, ⟨x.val, x.property, rfl⟩⟩
    rw [Q.partial_projection p x] at h
    exact h.symm
  obtain ⟨β, hβ, _⟩ := NativeTransport.old_prescribed S H J A0 B overA0 W p dom ran γ compatible
  exact ⟨β, hβ⟩

variable (cco : SemanticCCO.{0,v,v,w} S) (normalized : NoFiniteExactKernel S)
variable (D : Direction S) (unique : ∀ E : Direction S, E = D)

include cco normalized unique in
theorem relative_acl (A : Finset M) :
    FiniteLift.aclSet G (↑A : Set M) = RealClosure.Bounds.packetClosure S H A :=
  (fullRealAcl_eq S H A).symm.trans
    (normalized_absolute_acl S H (semanticCCO_change_universe S cco) normalized D unique A)

include cco normalized unique in
/-- Root and extension clauses use precisely the fixed B028 carrier;
absolute closure is proved from its full actual packets, not inferred
from the weaker inclusion of the input closure. -/
theorem relative_plain_closed (ep : CoarseEPPAFor S H J A0 B) :
    Witness S G safe (↑A0) W.carrier ∧ FiniteLift.aclSet G W.carrier = W.carrier := by
  have aclA := relative_acl S H cco normalized D unique A0
  refine ⟨⟨W.finite, ?_, relative_ordinary S H J A0 B overA0 W ep, ?_⟩, ?_⟩
  · rw [aclA]
    exact W.contains
  · intro Z hZ z hz
    have unsafeZ : UnsafeSet S (Subtype.val : W.carrier → M) safe Z := by
      intro x hx y hy ne a hcol ha
      exact hZ.2 x hx y hy ne ⟨a, ha, hcol⟩
    obtain ⟨β, image, root⟩ := W.rooted Z unsafeZ z hz
    refine ⟨β, ?_, root⟩
    intro x hx
    rw [aclA]
    exact image x hx
  · apply Set.Subset.antisymm
    · intro x hx
      let U := W.finite.toFinset
      have hU : (↑U : Set M) = W.carrier := W.finite.coe_toFinset
      rw [← hU, relative_acl S H cco normalized D unique U] at hx
      obtain ⟨a, ha, hax⟩ := hx
      exact W.closed a (hU ▸ ha) x hax
    · exact FiniteLift.subset_aclSet G W.carrier

end
end CCO.RankInduction.Factors
