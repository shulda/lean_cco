import Mathlib.Basic.Finite.Prod
import Mathlib.Logic.Equiv.Sum

/-! Full indexed compatible carriers and their actual owner fibres.
These elementary set statements use no group action, orbitals, CCO, EPPA,
or ambient realization. Coordinate surjectivity does not require fullness
of the finite owner set. -/

namespace CCO.Owners.Joint

/-- Onto and jointly separating owner coordinates, with their literal
pairwise comparison maps. Fullness is a separate predicate below. -/
structure OwnerDiagram (I B : Type*) (Bi : I → Type*) where
  beta : ∀ i, B → Bi i
  beta_surjective : ∀ i, Function.Surjective (beta i)
  jointly_injective : ∀ b c, (∀ i, beta i b = beta i c) → b = c
  Comparison : I → I → Type*
  left : ∀ i j, Bi i → Comparison i j
  right : ∀ i j, Bi j → Comparison i j
  commute : ∀ b i j, left i j (beta i b) = right i j (beta j b)

variable {I B : Type*} {Bi : I → Type*}
variable (d : OwnerDiagram I B Bi)

/-- Literal agreement in every specified pairwise comparison carrier. -/
def CompatibleOwner (b : ∀ i, Bi i) : Prop :=
  ∀ i j, d.left i j (b i) = d.right i j (b j)

/-- No compatible finite owner tuple is omitted. This is stronger than
surjectivity of the individual owner-coordinate maps. -/
def FullOwners : Prop :=
  ∀ b, CompatibleOwner d b → ∃ c, ∀ i, d.beta i c = b i

/-- Every actual owner passes the pairwise tests; the converse is not used. -/
theorem compatible_beta (b : B) : CompatibleOwner d (fun i => d.beta i b) :=
  d.commute b

variable (Di : I → Type*) (own : ∀ i, Di i → Bi i)

/-- ALL compatible coordinate tuples, with repeated indices retained. -/
abbrev Carrier := {x : ∀ i, Di i // CompatibleOwner d (fun i => own i (x i))}

instance carrier_finite [Finite I] [∀ i, Finite (Di i)] : Finite (Carrier d Di own) :=
  inferInstance

/-- A tuple above one specified owner lies in the full compatible carrier. -/
def overOwner (b : B) (x : ∀ i, {a : Di i // own i a = d.beta i b}) :
    Carrier d Di own :=
  ⟨fun i => (x i).val, by
    intro i j
    change d.left i j (own i (x i).val) = d.right i j (own j (x j).val)
    rw [(x i).property, (x j).property]
    exact d.commute b i j⟩

/-- C05: complete a prescribed coordinate using ONE actual owner b.
In particular this proof does not use `FullOwners`. -/
theorem coordinate_surjective
    (surjOwn : ∀ i, Function.Surjective (own i)) (i : I) :
    Function.Surjective (fun w : Carrier d Di own => w.val i) := by
  classical
  intro a
  obtain ⟨b, hb⟩ := d.beta_surjective i (own i a)
  let x : ∀ j, {a : Di j // own j a = d.beta j b} := fun j =>
    ⟨Classical.choose (surjOwn j (d.beta j b)), Classical.choose_spec (surjOwn j (d.beta j b))⟩
  let y : ∀ j, {a : Di j // own j a = d.beta j b} :=
    Function.update x i ⟨a, hb.symm⟩
  exact ⟨overOwner d Di own b y, by simp [overOwner, y]⟩

/-- Finite owner fullness supplies the unique complete owner of a tuple. -/
noncomputable def owner (full : FullOwners d) (w : Carrier d Di own) : B :=
  Classical.choose (full (fun i => own i (w.val i)) w.property)

@[simp] theorem beta_owner (full : FullOwners d) (w : Carrier d Di own) (i : I) :
    d.beta i (owner d Di own full w) = own i (w.val i) :=
  Classical.choose_spec (full (fun i => own i (w.val i)) w.property) i

/-- Joint separation identifies the chosen owner with any prescribed one. -/
theorem owner_eq (full : FullOwners d) (w : Carrier d Di own) (b : B)
    (h : ∀ i, own i (w.val i) = d.beta i b) : owner d Di own full w = b :=
  d.jointly_injective _ _ (fun i => (beta_owner d Di own full w i).trans (h i))

@[simp] theorem owner_overOwner (full : FullOwners d) (b : B)
    (x : ∀ i, {a : Di i // own i a = d.beta i b}) :
    owner d Di own full (overOwner d Di own b x) = b :=
  owner_eq d Di own full _ b (fun i => (x i).property)

/-- C04: onto owner map, before any use of a nonempty action criterion. -/
theorem owner_surjective (full : FullOwners d)
    (surjOwn : ∀ i, Function.Surjective (own i)) :
    Function.Surjective (owner d Di own full) := by
  intro b
  let x : ∀ i, {a : Di i // own i a = d.beta i b} := fun i =>
    ⟨Classical.choose (surjOwn i (d.beta i b)), Classical.choose_spec (surjOwn i (d.beta i b))⟩
  exact ⟨overOwner d Di own b x, owner_overOwner d Di own full b x⟩

/-- C03: an owner fibre is the FULL independent product of its displayed
coordinate fibres. This is a carrier identity, not an action decomposition. -/
noncomputable def owner_fibre_equiv (full : FullOwners d) (b : B) :
    {w : Carrier d Di own // owner d Di own full w = b} ≃
      (∀ i, {a : Di i // own i a = d.beta i b}) where
  toFun w i := ⟨w.val.val i, by
    rw [← beta_owner d Di own full w.val i, w.property]⟩
  invFun x := ⟨overOwner d Di own b x, owner_overOwner d Di own full b x⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    funext i
    rfl

/-- Equivalent disjoint-union description, retaining ALL owner fibres. -/
noncomputable def carrier_sigma_equiv (full : FullOwners d) :
    Carrier d Di own ≃ (b : B) × (∀ i, {a : Di i // own i a = d.beta i b}) :=
  (Equiv.sigmaFiberEquiv (owner d Di own full)).symm.trans
    (Equiv.sigmaCongrRight (owner_fibre_equiv d Di own full))

/-- With full owners, the coordinate witness is nonempty exactly when its
owner is; empty owners are handled without a group-action argument. -/
theorem nonempty_carrier_iff (full : FullOwners d)
    (surjOwn : ∀ i, Function.Surjective (own i)) :
    Nonempty (Carrier d Di own) ↔ Nonempty B := by
  constructor
  · rintro ⟨w⟩; exact ⟨owner d Di own full w⟩
  · rintro ⟨b⟩
    obtain ⟨w, _⟩ := owner_surjective d Di own full surjOwn b
    exact ⟨w⟩

include d in
/-- Even without full owners, an empty actual owner forces every image
coordinate empty, using its actual surjectivity. -/
theorem isEmpty_owner_coordinate [IsEmpty B] (i : I) : IsEmpty (Bi i) :=
  ⟨fun b => by obtain ⟨a, _⟩ := d.beta_surjective i b; exact isEmptyElim a⟩

include d own in
/-- The factor cannot map to an empty actual owner coordinate. -/
theorem isEmpty_coordinate [IsEmpty B] (i : I) : IsEmpty (Di i) :=
  ⟨fun x => (isEmpty_owner_coordinate d i).false (own i x)⟩

/-- C02: nonempty index families of empty factors have empty full carrier.
No finite-owner fullness, EPPA, or point-action premise is required. -/
theorem isEmpty_carrier [Nonempty I] [IsEmpty B] : IsEmpty (Carrier d Di own) :=
  ⟨fun w => (isEmpty_coordinate d Di own (Classical.choice ‹Nonempty I›)).false
    (w.val (Classical.choice ‹Nonempty I›))⟩

end CCO.Owners.Joint
