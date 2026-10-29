import CCO.Owners.Master.RelativeExact
import CCO.Owners.Master.PacketCongruence
import CCO.Owners.Provider.Canonical

/-! The actual local owner callback at every owner-master stage. The
source, exact relative kernel and target packet language are constructed;
ordinary EPPA of the CURRENT original exact quotient remains the stated
conditional input. -/

universe v w t
namespace CCO.Owners.Master

open RawExact ExactCRT CanonicalQuotients
open RealClosure.Bounds Provider Product

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (E F : ExactEq S H cco ()) (hEF : E ≤ F)

local instance callbackInvariantE : Invariant G E.val := Product.exactInvariant S H cco E
local instance callbackInvariantF : Invariant G F.val := Product.exactInvariant S H cco F

/-- One genuine finite packet-closed owner witness over the ENTIRE given
target base. All compatible sparse/empty/singleton requests and all
prescribed point motions are the actual `OwnerWitness` conclusions. -/
theorem relative_owner_provider (ep : OrdinaryEPPA G (Quotient E.val))
    (B : Set (Quotient F.val)) (finiteB : B.Finite) (nonemptyB : B.Nonempty)
    (closedB : ∀ u ∈ B, ∀ v,
      finitePacket (quotientSource S H cco F) (quotientSource_homogeneous S H cco F) u v → v ∈ B)
    (T : Set (Quotient E.val)) (finiteT : T.Finite)
    (overT : ∀ x : T, Abstract.quotientMap hEF x.val ∈ B) :
    Nonempty (OwnerWitness (quotientSource S H cco E) (quotientSource_homogeneous S H cco E)
      (Abstract.quotientMap hEF) (Product.quotientMap_equivariant hEF) B T overT) := by
  letI := quotientSource_countable S H cco E
  apply actual_owner_witness (quotientSource S H cco E) (quotientSource_homogeneous S H cco E)
    (quotientSource_cco S H cco E) ep (Abstract.quotientMap hEF)
    (Abstract.quotientMap_surjective hEF) (Product.quotientMap_equivariant hEF)
    (relativeExact S H cco E F hEF) (relativeExact_kernel S H cco E F hEF)
    B finiteB nonemptyB _ T finiteT overT
  intro u hu v huv
  exact closedB u hu v ((relative_ownerPacket S H cco E F hEF u v).mp huv)

end CCO.Owners.Master
