import CCO.Owners.Joint.Source

/-! Downstream consumers use the actual original witness and full owner
action, rather than restating the abstract finite assembly signature. -/
universe u v w t z
namespace CCO.Owners.Joint.Consumers
open CCO.Owners.Product
open RawExact ExactCRT RawExact.CanonicalQuotients
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable {i : ι} {I : Type z} [Finite I] [Nonempty I]
variable (C T : I → ExactEq S H cco i) (hCT : ∀ k, C k ≤ T k)
variable (meet_id : ∀ x y : X i, (∀ k, (C k).val x y) → x = y)
variable (gate : ∀ k l, k ≠ l → (C k).val ⊔ (C l).val = (T k).val ⊔ (T l).val)
local instance invariantC (k : I) : Invariant G (C k).val := Product.exactInvariant S H cco (C k)
local instance invariantT (k : I) : Invariant G (T k).val := Product.exactInvariant S H cco (T k)

variable (B : Set (Quotient (Abstract.familyMeet (fun k => (T k).val))))
variable (D : ∀ k, Set (Quotient (C k).val))
variable (hD : ∀ k (d : D k), (actualGeometry S H cco C T hCT meet_id gate).own k d.val ∈ (actualGeometry S H cco C T hCT meet_id gate).OwnerImage B k)
variable (surjD : ∀ k, Function.Surjective ((actualGeometry S H cco C T hCT meet_id gate).finiteOwn B D hD k))
variable (fullB : FullOwners ((actualGeometry S H cco C T hCT meet_id gate).finiteDiagram B))


variable [sourceCountable : Countable (X i)]
include sourceCountable

/-- A downstream orbit classification in the ACTUAL original finite
witness: two real points share an automorphism orbit exactly when their
complete joint owners share a FULL owner automorphism orbit. -/
theorem real_point_orbits
    (factorLift : ∀ k, GroupActions.PrescribedLift
      ((actualGeometry S H cco C T hCT meet_id gate).factorAction B D hD surjD k) ((actualGeometry S H cco C T hCT meet_id gate).finiteOwn B D hD k))
    (x y : (actualGeometry S H cco C T hCT meet_id gate).inducedCarrier D) :
    (∃ a : OrbitalAut G (X i) (Subtype.val : (actualGeometry S H cco C T hCT meet_id gate).inducedCarrier D → X i), a.val x = y) ↔
      ∃ g : OrbitalAut G (Quotient (Abstract.familyMeet (fun k => (T k).val)))
        (Subtype.val : B → _),
        g.val (((actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB).projection x) =
          ((actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB).projection y := by
  let QO := (actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨QO.action a,?_⟩
    rw [QO.action_projection,ha]
  · rintro ⟨g,hg⟩
    obtain ⟨a,_,haxy⟩ := Actual.prescribed_point S H cco C T hCT meet_id gate
      B D hD surjD fullB factorLift x y g hg
    exact ⟨a,haxy⟩

/-- A real point request in ONE complete owner fibre has a structural
solution fixing EVERY owner, including owners outside the request. The
last clause translates the abstract kernel back to the literal Hstar map. -/
theorem real_fibre_motion
    (factorLift : ∀ k, GroupActions.PrescribedLift
      ((actualGeometry S H cco C T hCT meet_id gate).factorAction B D hD surjD k) ((actualGeometry S H cco C T hCT meet_id gate).finiteOwn B D hD k))
    (x y : (actualGeometry S H cco C T hCT meet_id gate).inducedCarrier D)
    (sameOwner : (actualGeometry S H cco C T hCT meet_id gate).joint x.val = (actualGeometry S H cco C T hCT meet_id gate).joint y.val) :
    ∃ a : OrbitalAut G (X i) (Subtype.val : (actualGeometry S H cco C T hCT meet_id gate).inducedCarrier D → X i),
      a.val x = y ∧ ((actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB).action a = 1 ∧
      ∀ z : (actualGeometry S H cco C T hCT meet_id gate).inducedCarrier D, (actualGeometry S H cco C T hCT meet_id gate).joint (a.val z).val = (actualGeometry S H cco C T hCT meet_id gate).joint z.val := by
  let QO := (actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB
  have hxy : QO.projection x = QO.projection y := by
    apply Subtype.ext
    exact (QO.commutes x).trans (sameOwner.trans (QO.commutes y).symm)
  obtain ⟨a,ha,hamove⟩ := (Actual.onto_and_kernel S H cco C T hCT meet_id gate
    B D hD surjD fullB factorLift).2 x y hxy
  refine ⟨a,hamove,ha,?_⟩
  intro z
  calc
    _ = (QO.projection (a.val z)).val := (QO.commutes _).symm
    _ = ((QO.action a).val (QO.projection z)).val :=
      congrArg Subtype.val (QO.action_projection a z).symm
    _ = (QO.projection z).val := by rw [ha]; rfl
    _ = _ := QO.commutes z

end CCO.Owners.Joint.Consumers
