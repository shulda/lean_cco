import CCO.Owners.Master.QuotientSources
import CCO.Owners.Provider.PacketProjection

/-! Greatest finite packets depend on the actual pair action, rather
than on the choice of names for its canonical orbitals. This identifies
the actual target packet with the owner's complete orbital packet. -/

universe v w r t
namespace CCO.Owners.Master

open ParityHasse.Original RealClosure.Bounds
open Provider.OrbitalPackets

section PairPackets
variable {M : Type v} {G : Type t} [Group G] [MulAction G M]
variable (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (T : AtomicSource.{0,v,r} Unit (fun _ => M))

/-- No higher homogeneity, quotient exactness or global lifting premise
is used in this palette-independent packet identification. -/
theorem packet_eq_of_pairActions
    (PS : PairAction S (G := G)) (PT : PairAction T (G := G)) :
    PS.packet.val = PT.packet.val := by
  let FS : ColourEq T () := ⟨PS.packet.val,
    PT.colour_invariant (PS.group_invariant PS.packet.property)⟩
  let FT : ColourEq S () := ⟨PT.packet.val,
    PS.colour_invariant (PT.group_invariant PT.packet.property)⟩
  have hFS : FS ≤ PT.packet := PT.le_packet FS PS.packet_finite
  have hFT : FT ≤ PS.packet := PS.le_packet FT PT.packet_finite
  exact le_antisymm hFS hFT

def pairAction_of_homogeneous (H : HomogeneousSource S G) : PairAction S (G := G) where
  invariant := S.colourInvariant_of_homogeneous H
  homogeneous x y x' y' hc := S.pair_homogeneous_of_homogeneous H x x' y y' hc

end PairPackets

section Actual
open RawExact ExactCRT CanonicalQuotients
variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (E F : ExactEq S H cco ()) (hEF : E ≤ F)

local instance actualInvariantE : Invariant G E.val := Product.exactInvariant S H cco E
local instance actualInvariantF : Invariant G F.val := Product.exactInvariant S H cco F

theorem relative_ownerPacket (x y : Quotient F.val) :
    Provider.ownerPacket (quotientSource S H cco E) (quotientSource_homogeneous S H cco E)
      (Abstract.quotientMap hEF) (Abstract.quotientMap_surjective hEF)
      (Product.quotientMap_equivariant hEF) x y ↔
    finitePacket (quotientSource S H cco F) (quotientSource_homogeneous S H cco F) x y := by
  let TE := quotientSource S H cco E
  let HE := quotientSource_homogeneous S H cco E
  let TF := quotientSource S H cco F
  let HF := quotientSource_homogeneous S H cco F
  let ρ := Abstract.quotientMap hEF
  let onto := Abstract.quotientMap_surjective hEF
  let equivρ : ∀ (g : G) (x : Quotient E.val), ρ (g • x) = g • ρ x :=
    Product.quotientMap_equivariant hEF
  let P := pairAction_of_homogeneous TF HF
  have heq := packet_eq_of_pairActions TF (Provider.ownerSource TE HE ρ onto equivρ)
    P (Provider.ownerPairAction TE HE ρ onto equivρ)
  rw [P.packet_eq_accepted HF] at heq
  change (Provider.ownerPairAction TE HE ρ onto equivρ).packet.val x y ↔
    (finitePacket TF HF).val x y
  rw [heq]

/-- The full finite packet of an actual quotient projects into the full
finite packet of the actual coarser quotient, with all palette providers
discharged. -/
theorem relative_packet_projection (x y : Quotient E.val)
    (hxy : finitePacket (quotientSource S H cco E)
      (quotientSource_homogeneous S H cco E) x y) :
    finitePacket (quotientSource S H cco F) (quotientSource_homogeneous S H cco F)
      (Abstract.quotientMap hEF x) (Abstract.quotientMap hEF y) := by
  apply (relative_ownerPacket S H cco E F hEF _ _).mp
  exact Provider.packet_projection (quotientSource S H cco E)
    (quotientSource_homogeneous S H cco E) (Abstract.quotientMap hEF)
    (Abstract.quotientMap_surjective hEF) (Product.quotientMap_equivariant hEF) x y hxy

end Actual
end CCO.Owners.Master
