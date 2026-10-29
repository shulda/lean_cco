import CCO.Owners.Master.Assembly
import CCO.Owners.Master.MasterConsumers

/-! A constructed simultaneous provider is used for both a complete
finite coordinate request and a prescribed FULL target action, inside the
same finite real witness. No diagram or extension callback is supplied. -/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT Provider Product

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (T : Set A) (finiteT : T.Finite) (nonemptyT : T.Nonempty)
variable (ep : AllQuotientsEPPA S H cco)

def constructedMaster : ActualMaster.{v,w,t,z} S H cco T :=
  Classical.choice (actual_owner_master S H cco T finiteT nonemptyT ep)

local instance constructedConsumerInvariant (E : Exact S H cco) : CanonicalQuotients.Invariant G E.val :=
  Product.exactInvariant S H cco E

/-- The same actual constructed finite witness simultaneously realizes
ALL coordinates and lifts an ENTIRE prescribed finite target automorphism
on selected points. Repeated and empty coordinate families are included. -/
theorem constructed_coordinates_and_motion {I : Type z} [Fintype I]
    (E : I → Exact S H cco) (q : ∀ i, Quotient (E i).val)
    (member : ∀ i, q i ∈ (Quotient.mk'' : A → Quotient (E i).val) '' (constructedMaster.{v,w,t,z} S H cco T finiteT nonemptyT ep).carrier)
    (compat : Abstract.Compatible (fun i => (E i).val) q)
    (J K : Exact S H cco) (hJK : J ≤ K)
    (x y : (Quotient.mk'' : A → Quotient J.val) '' (constructedMaster.{v,w,t,z} S H cco T finiteT nonemptyT ep).carrier)
    (γ : OrbitalAut G (Quotient K.val)
      (Subtype.val : ((Quotient.mk'' : A → Quotient K.val) '' (constructedMaster.{v,w,t,z} S H cco T finiteT nonemptyT ep).carrier) → Quotient K.val))
    (motion : γ • (exactImageQuotient (G := G) (constructedMaster.{v,w,t,z} S H cco T finiteT nonemptyT ep).carrier J.val K.val hJK).projection x =
      (exactImageQuotient (G := G) (constructedMaster.{v,w,t,z} S H cco T finiteT nonemptyT ep).carrier J.val K.val hJK).projection y) :
    ∃ a ∈ (constructedMaster.{v,w,t,z} S H cco T finiteT nonemptyT ep).carrier, ∃ β : OrbitalAut G (Quotient J.val)
      (Subtype.val : ((Quotient.mk'' : A → Quotient J.val) '' (constructedMaster.{v,w,t,z} S H cco T finiteT nonemptyT ep).carrier) → Quotient J.val),
      (∀ i, Quotient.mk'' a = q i) ∧
      (exactImageQuotient (G := G) (constructedMaster.{v,w,t,z} S H cco T finiteT nonemptyT ep).carrier J.val K.val hJK).action β = γ ∧ β • x = y :=
  (constructedMaster.{v,w,t,z} S H cco T finiteT nonemptyT ep).coordinates_and_motion E q member compat J K hJK x y γ motion

end
end CCO.Owners.Master
