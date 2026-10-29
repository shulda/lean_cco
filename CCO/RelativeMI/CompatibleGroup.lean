import CCO.RelativeMI.FineSaturation
import CCO.SafeReadings.TransversalPure

/-! The FULL compatible fine-owner group and its honest coarse
homomorphism. Empty requests prove surjectivity; no section, selected
generator subgroup or faithful thin action is substituted. -/
universe v w t
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal AclOwners
open Owners.Product Owners.Provider ExactCRT RawExact SafeReadings

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (J : ColourEq S ()) (A0 : Finset M) (B : Finset (Coarse S H J))
variable (overA0 : ∀ x : ↥A0, coarseOwner S H J x.val ∈ B) (hEJ : R.E ≤ J)
local instance compatibleGroupFineAction : MulAction G (Owner S H R) := originalQuotientAction S H R.E
local instance compatibleGroupCoarseAction : MulAction G (Coarse S H J) := originalQuotientAction S H J

namespace FineStage
variable (F : FineStage S H R J A0 B overA0 hEJ)

def projection : ↥F.U → ↥B :=
  ownerProjection (fineProjection S H R J hEJ) (↑F.U) (↑B) F.over

def quotient : OrbitalQuotient (G := G)
    (Subtype.val : ↥F.U → Owner S H R) (Subtype.val : ↥B → Coarse S H J) :=
  inducedQuotient (fineProjection S H R J hEJ)
    (fineProjection_equivariant S H R J hEJ) (↑F.U) (↑B) F.over F.onto

/-- Membership uses EVERY fine automorphism inducing SOME complete
coarse automorphism, on ALL fine owners. -/
def Compatible (α : TransversalPure.Gamma S H R F.U) : Prop :=
  ∃ γ : OrbitalAut G (Coarse S H J) (Subtype.val : ↥B → Coarse S H J),
    ∀ q : ↥F.U, fineProjection S H R J hEJ (α.val q).val =
      (γ.val (F.projection S H R J A0 B overA0 hEJ q)).val

/-- In this ACTUAL recognized quotient, every fine induced automorphism
descends. This is a theorem from equivariance and full coarse coverage. -/
theorem every_fine_compatible (α : TransversalPure.Gamma S H R F.U) :
    F.Compatible S H R J A0 B overA0 hEJ α := by
  refine ⟨(F.quotient S H R J A0 B overA0 hEJ).action α,?_⟩
  intro q
  exact (congrArg Subtype.val
    ((F.quotient S H R J A0 B overA0 hEJ).action_projection α q)).symm

def compatibleGroup : Subgroup (TransversalPure.Gamma S H R F.U) where
  carrier := F.Compatible S H R J A0 B overA0 hEJ
  one_mem' := F.every_fine_compatible S H R J A0 B overA0 hEJ 1
  mul_mem' := by
    intro α β _ _
    exact F.every_fine_compatible S H R J A0 B overA0 hEJ (α*β)
  inv_mem' := by
    intro α _
    exact F.every_fine_compatible S H R J A0 B overA0 hEJ α⁻¹

theorem mem_compatibleGroup (α : TransversalPure.Gamma S H R F.U) :
    α ∈ F.compatibleGroup S H R J A0 B overA0 hEJ :=
  F.every_fine_compatible S H R J A0 B overA0 hEJ α

def coarseHom : F.compatibleGroup S H R J A0 B overA0 hEJ →*
    OrbitalAut G (Coarse S H J) (Subtype.val : ↥B → Coarse S H J) :=
  (F.quotient S H R J A0 B overA0 hEJ).action.comp
    (F.compatibleGroup S H R J A0 B overA0 hEJ).subtype

theorem coarseHom_projection (δ : F.compatibleGroup S H R J A0 B overA0 hEJ) (q : ↥F.U) :
    (F.coarseHom S H R J A0 B overA0 hEJ δ).val
      (F.projection S H R J A0 B overA0 hEJ q) =
        F.projection S H R J A0 B overA0 hEJ (δ.val.val q) :=
  (F.quotient S H R J A0 B overA0 hEJ).action_projection δ.val q

/-- Every original request has its ENTIRE fine component in the full
group, with the original prescribed coarse component unchanged. -/
theorem prescribed (r : OriginalRequest S H J A0 B overA0) :
    ∃ δ : F.compatibleGroup S H R J A0 B overA0 hEJ,
      F.coarseHom S H R J A0 B overA0 hEJ δ = r.owner ∧
      ∀ x : r.part.domain,
        (δ.val.val ⟨owner S H R x.val.val,
          F.contains x.val.val ⟨x.val.val,x.val.property,(finitePacket S H).val.refl _⟩⟩).val =
            owner S H R (r.part.map x).val := by
  obtain ⟨α,hα,hown⟩ := F.extensions r
  have hc : (F.quotient S H R J A0 B overA0 hEJ).action α = r.owner := by
    apply induced_owner_unique (fineProjection S H R J hEJ)
      (fineProjection_equivariant S H R J hEJ) (↑F.U) (↑B) F.over F.onto α r.owner
    intro q
    exact Subtype.ext (hown q).symm
  exact ⟨⟨α,F.mem_compatibleGroup S H R J A0 B overA0 hEJ α⟩,hc,hα⟩

/-- ALL empty real domains, not a chosen list of nonempty requests,
give surjectivity. No coherent choice of lifts is made. -/
theorem coarseHom_surjective : Function.Surjective (F.coarseHom S H R J A0 B overA0 hEJ) := by
  intro γ
  obtain ⟨δ,hδ,_⟩ := F.prescribed S H R J A0 B overA0 hEJ
    (emptyRequest (coarseOwner S H J) (↑A0) (↑B) overA0 γ)
  exact ⟨δ,hδ⟩

variable [Infinite M]
omit [Infinite M] in
/-- The actual diagonal thin owners all belong, even when their owner
action has a kernel. -/
theorem diagonal_mem (e : ResidualData.PacketGroup S H) :
    TransversalPure.diagonal S H R F.U F.invariant e ∈
      F.compatibleGroup S H R J A0 B overA0 hEJ :=
  F.mem_compatibleGroup S H R J A0 B overA0 hEJ _

/-- Original lifting proves commutation for EVERY member of the full
compatible group, rather than only for selected extension generators. -/
theorem compatible_commute (δ : F.compatibleGroup S H R J A0 B overA0 hEJ)
    (e : ResidualData.PacketGroup S H) (q : ↥F.U) :
    δ.val.val (TransversalGauge.moveOwner S H R F.U F.invariant e q) =
      TransversalGauge.moveOwner S H R F.U F.invariant e (δ.val.val q) :=
  TransversalPure.commute S H R F.U F.invariant δ.val e q

omit [Infinite M] in
theorem nonempty_owners (hne : A0.Nonempty) : F.U.Nonempty := by
  obtain ⟨a,ha⟩ := hne
  exact ⟨owner S H R a,F.contains a ⟨a,ha,(finitePacket S H).val.refl _⟩⟩

end FineStage
end
end CCO.RelativeMI
