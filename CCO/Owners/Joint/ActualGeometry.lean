import CCO.Owners.Joint.ActualKernel
import CCO.Owners.Joint.Geometry

/-! C06–09: every ambient field of the finite assembly is supplied by
literal original exact quotient carriers. No tuple-realization or readout
provider remains an additional source hypothesis. -/
universe u v w t z
namespace CCO.Owners.Joint
open RawExact ExactCRT RawExact.CanonicalQuotients

section Maps
variable {A : Type*} {E F K : Setoid A}
theorem quotientMap_comp (h : E ≤ F) (k : F ≤ K) (q : Quotient E) :
    Abstract.quotientMap k (Abstract.quotientMap h q) =
      Abstract.quotientMap (h.trans k) q := by
  induction q using Quotient.inductionOn with | _ x => rfl
end Maps

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable {i : ι} {I : Type z} [Finite I]
variable (C T : I → ExactEq S H cco i)
variable (hCT : ∀ k, C k ≤ T k)

/-- The literal joint-owner quotient, with its literal projected classes. -/
def actualOwnerDiagram : OwnerDiagram I
    (Quotient (Abstract.familyMeet (fun k => (T k).val)))
    (fun k => Quotient (T k).val) where
  beta k := Abstract.quotientMap (show Abstract.familyMeet (fun l => (T l).val) ≤
    (T k).val from fun _ _ h => h k)
  beta_surjective _ := Abstract.quotientMap_surjective _
  jointly_injective b c h := Abstract.coordinates_injective (fun k => (T k).val) (funext h)
  Comparison k l := Quotient ((T k).val ⊔ (T l).val)
  left _ _ := Abstract.quotientMap le_sup_left
  right _ _ := Abstract.quotientMap le_sup_right
  commute b _ _ := by
    induction b using Quotient.inductionOn with | _ x => rfl

def actualOwn (k : I) : Quotient (C k).val → Quotient (T k).val :=
  Abstract.quotientMap (hCT k)

theorem actual_owner_compatible_iff (q : ∀ k, Quotient (C k).val) :
    CompatibleOwner (actualOwnerDiagram S H cco T)
      (fun k => actualOwn S H cco C T hCT k (q k)) ↔
      ActualCompatible S H cco C T hCT q := by
  unfold CompatibleOwner ActualCompatible actualOwnerDiagram actualOwn
  simp only [quotientMap_comp]

noncomputable def actualPointEquiv
    (meet_id : ∀ x y : X i, (∀ k, (C k).val x y) → x = y)
    (gate : ∀ k l, k ≠ l → (C k).val ⊔ (C l).val = (T k).val ⊔ (T l).val) :
    X i ≃ Carrier (actualOwnerDiagram S H cco T)
      (fun k => Quotient (C k).val) (actualOwn S H cco C T hCT) :=
  Equiv.ofBijective (fun x => ⟨fun k => Quotient.mk (C k).val x, fun _ _ => rfl⟩)
    ⟨fun x y h => original_coordinates_injective S H cco C meet_id
      (congrArg Subtype.val h), by
      intro q
      obtain ⟨x,hx⟩ := actual_tuple_realization S H cco C T hCT gate q.val
        ((actual_owner_compatible_iff S H cco C T hCT q.val).mp q.property)
      exact ⟨x,Subtype.ext (funext hx)⟩⟩

section Actions
variable [∀ k, Invariant G (C k).val] [∀ k, Invariant G (T k).val]

/-- The original source supplies the entire tuple geometry. The two real
assumptions here are precisely meet C=Id and JOG; no finite witness data
or additional group action identity is assumed. -/
noncomputable def actualGeometry
    (meet_id : ∀ x y : X i, (∀ k, (C k).val x y) → x = y)
    (gate : ∀ k l, k ≠ l → (C k).val ⊔ (C l).val = (T k).val ⊔ (T l).val) :
    AmbientGeometry (G := G) (A := X i)
      (Q := fun k => Quotient (C k).val) (O := fun k => Quotient (T k).val)
      (Ω := Quotient (Abstract.familyMeet (fun k => (T k).val))) where
  diagram := actualOwnerDiagram S H cco T
  own := actualOwn S H cco C T hCT
  coordinate k := Quotient.mk (C k).val
  joint := Quotient.mk (Abstract.familyMeet (fun k => (T k).val))
  equiv_own _ := Product.quotientMap_equivariant _
  equiv_coordinate _ _ _ := rfl
  equiv_joint _ _ := rfl
  equiv_beta k := Product.quotientMap_equivariant
    (show Abstract.familyMeet (fun l => (T l).val) ≤ (T k).val from fun _ _ h => h k)
  joint_commute _ _ := rfl
  full := actualPointEquiv S H cco C T hCT meet_id gate
  full_apply _ _ := rfl
  fine := original_fine_readout S H cco C meet_id

end Actions

/-- Original exactness constructs the action invariance instances too.
This is the source-level entry point, with no uninstantiated invariance
or tuple-geometry provider. -/
noncomputable def canonicalGeometry
    (meet_id : ∀ x y : X i, (∀ k, (C k).val x y) → x = y)
    (gate : ∀ k l, k ≠ l → (C k).val ⊔ (C l).val = (T k).val ⊔ (T l).val) :
    letI : ∀ k, Invariant G (C k).val := fun k => Product.exactInvariant S H cco (C k)
    letI : ∀ k, Invariant G (T k).val := fun k => Product.exactInvariant S H cco (T k)
    AmbientGeometry (G := G) (A := X i)
      (Q := fun k => Quotient (C k).val) (O := fun k => Quotient (T k).val)
      (Ω := Quotient (Abstract.familyMeet (fun k => (T k).val))) := by
  letI : ∀ k, Invariant G (C k).val := fun k => Product.exactInvariant S H cco (C k)
  letI : ∀ k, Invariant G (T k).val := fun k => Product.exactInvariant S H cco (T k)
  exact actualGeometry S H cco C T hCT meet_id gate

end CCO.Owners.Joint
