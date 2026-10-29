import CCO.Owners.Joint.Carrier
import CCO.GroupActions
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Group.Hom.Defs

/-! Indexed matching groups and their literal full tuple actions. These
elementary action lemmas make no fine-language or source hypothesis. -/
namespace CCO.Owners.Joint
variable {I Γ : Type*} {K R : I → Type*}
variable [Group Γ] [∀ i, Group (K i)] [∀ i, Group (R i)]

def matchingGroup (own : ∀ i, K i →* R i) (rho : ∀ i, Γ →* R i) :
    Subgroup (Γ × (∀ i, K i)) where
  carrier := {p | ∀ i, own i (p.2 i) = rho i p.1}
  one_mem' := by intro i; simp
  mul_mem' := by
    intro a b ha hb i
    change own i (a.2 i * b.2 i) = rho i (a.1 * b.1)
    simp only [map_mul, ha i, hb i]
  inv_mem' := by
    intro a ha i
    change own i (a.2 i)⁻¹ = rho i a.1⁻¹
    simp only [map_inv, ha i]

abbrev Matching (own : ∀ i, K i →* R i) (rho : ∀ i, Γ →* R i) :=
  ↥(matchingGroup own rho)

def matchingOwner (own : ∀ i, K i →* R i) (rho : ∀ i, Γ →* R i) :
    Matching own rho →* Γ where
  toFun k := k.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

def matchingCoordinate (own : ∀ i, K i →* R i) (rho : ∀ i, Γ →* R i) :
    Matching own rho →* (∀ i, K i) where
  toFun k := k.val.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Uniqueness of the ENTIRE common owner component. -/
theorem matchingCoordinate_injective
    (own : ∀ i, K i →* R i) (rho : ∀ i, Γ →* R i)
    (joint : Function.Injective (fun g : Γ => fun i => rho i g)) :
    Function.Injective (matchingCoordinate own rho) := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · apply joint
    funext i
    exact (a.property i).symm.trans
      ((congrArg (own i) (congrFun hab i)).trans (b.property i))
  · exact hab

/-- The source's existential coordinate-tuple presentation is itself a
subgroup, and forgetting the unique common owner gives an isomorphism. -/
def coordinateGroup (own : ∀ i, K i →* R i) (rho : ∀ i, Γ →* R i) :
    Subgroup (∀ i, K i) := (matchingGroup own rho).map (MonoidHom.snd Γ (∀ i, K i))

theorem mem_coordinateGroup (own : ∀ i, K i →* R i) (rho : ∀ i, Γ →* R i)
    (a : ∀ i, K i) : a ∈ coordinateGroup own rho ↔ ∃ g, ∀ i, own i (a i) = rho i g := by
  constructor
  · rintro ⟨p,hp,hpa⟩
    change p.2 = a at hpa
    exact ⟨p.1,fun i => by rw [← hpa]; exact hp i⟩
  · rintro ⟨g,hg⟩
    exact ⟨(g,a),hg,rfl⟩

noncomputable def matchingCoordinatesEquiv
    (own : ∀ i, K i →* R i) (rho : ∀ i, Γ →* R i)
    (joint : Function.Injective (fun g : Γ => fun i => rho i g)) :
    Matching own rho ≃* ↥(coordinateGroup own rho) :=
  MulEquiv.ofBijective ({
    toFun := fun k => ⟨k.val.2, ⟨k.val,k.property,rfl⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl } : Matching own rho →* ↥(coordinateGroup own rho))
    ⟨fun a b h => matchingCoordinate_injective own rho joint (congrArg Subtype.val h), by
      intro a
      obtain ⟨g,hg⟩ := (mem_coordinateGroup own rho a.val).mp a.property
      exact ⟨⟨(g,a.val),hg⟩,rfl⟩⟩

section Actions
variable {B : Type*} {Bi Di : I → Type*}
variable [MulAction Γ B] [∀ i, MulAction (R i) (Bi i)] [∀ i, MulAction (K i) (Di i)]
variable (d : OwnerDiagram I B Bi) (full : FullOwners d)
variable (π : ∀ i, Di i → Bi i)
variable (own : ∀ i, K i →* R i) (rho : ∀ i, Γ →* R i)
variable (eqπ : ∀ i g x, π i (g • x) = own i g • π i x)
variable (eqβ : ∀ i g b, d.beta i (g • b) = rho i g • d.beta i b)

include eqπ eqβ

theorem matching_owner_coordinate (k : Matching own rho) (w : Carrier d Di π) (i : I) :
    π i (k.val.2 i • w.val i) = d.beta i (k.val.1 • owner d Di π full w) := by
  rw [eqπ, k.property i, eqβ, beta_owner]

@[instance_reducible] def witnessAction : MulAction (Matching own rho) (Carrier d Di π) where
  smul k w := ⟨fun i => k.val.2 i • w.val i, by
    intro i j
    change d.left i j (π i (k.val.2 i • w.val i)) =
      d.right i j (π j (k.val.2 j • w.val j))
    rw [matching_owner_coordinate d full π own rho eqπ eqβ,
      matching_owner_coordinate d full π own rho eqπ eqβ]
    exact d.commute _ i j⟩
  one_smul w := by
    apply Subtype.ext
    funext i
    exact one_smul _ _
  mul_smul k l w := by
    apply Subtype.ext
    funext i
    exact mul_smul _ _ _

theorem owner_smul (k : Matching own rho) (w : Carrier d Di π) :
    letI := witnessAction d full π own rho eqπ eqβ
    owner d Di π full (k • w) = k.val.1 • owner d Di π full w := by
  letI := witnessAction d full π own rho eqπ eqβ
  apply owner_eq
  exact matching_owner_coordinate d full π own rho eqπ eqβ k w

/-- C17 at the matching-action level: all factors use the SAME prescribed
joint-owner action, on their entire owner sets. -/
theorem matching_prescribed
    (lift : ∀ i, GroupActions.PrescribedLift (own i) (π i)) :
    letI := witnessAction d full π own rho eqπ eqβ
    GroupActions.PrescribedLift (matchingOwner own rho) (owner d Di π full) := by
  letI := witnessAction d full π own rho eqπ eqβ
  intro x y g hg
  have hi : ∀ i, rho i g • π i (x.val i) = π i (y.val i) := by
    intro i
    rw [← beta_owner d Di π full x i, ← eqβ, hg, beta_owner]
  choose a ha hmove using (fun i => lift i (x.val i) (y.val i) (rho i g) (hi i))
  refine ⟨⟨(g,a),ha⟩,rfl,?_⟩
  apply Subtype.ext
  funext i
  exact hmove i

end Actions
end CCO.Owners.Joint
