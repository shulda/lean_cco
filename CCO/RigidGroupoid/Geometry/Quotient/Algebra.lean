import CCO.ExactCRT.TypedPullback

/-! Faithful quotient relation algebra for actual surjective maps.
This is represented relation algebra, with no exactness or group assumptions. -/

namespace CCO.RigidGroupoid.Geometry.Quotient

open RawExact

section Relations
variable {A B C Q R U : Type*}

def image (π : A → Q) (σ : B → R) (D : A → B → Prop) : Q → R → Prop :=
  fun q r => ∃ a b, π a = q ∧ σ b = r ∧ D a b

def Bisaturated (π : A → Q) (σ : B → R) (D : A → B → Prop) : Prop :=
  (fun x y => ∃ b, (∃ a, π x = π a ∧ D a b) ∧ σ b = σ y) = D

theorem pullback_image (π : A → Q) (σ : B → R) (D : A → B → Prop) :
    GroupActions.pullback π σ (image π σ D) =
      (fun x y => ∃ b, (∃ a, π x = π a ∧ D a b) ∧ σ b = σ y) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨a,b,ha,hb,hab⟩
    exact ⟨b,⟨a,ha.symm,hab⟩,hb⟩
  · rintro ⟨b,⟨a,ha,hab⟩,hb⟩
    exact ⟨a,b,ha.symm,hb,hab⟩

theorem image_pullback (π : A → Q) (σ : B → R)
    (surjπ : Function.Surjective π) (surjσ : Function.Surjective σ)
    (D : Q → R → Prop) : image π σ (GroupActions.pullback π σ D) = D := by
  funext q r
  apply propext
  constructor
  · rintro ⟨a,b,rfl,rfl,hab⟩
    exact hab
  · intro hqr
    obtain ⟨a,rfl⟩ := surjπ q
    obtain ⟨b,rfl⟩ := surjσ r
    exact ⟨a,b,rfl,rfl,hqr⟩

theorem pullback_bisaturated (π : A → Q) (σ : B → R) (D : Q → R → Prop) :
    Bisaturated π σ (GroupActions.pullback π σ D) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨b,⟨a,ha,hab⟩,hb⟩
    change π x = π a at ha
    change σ b = σ y at hb
    change D (π a) (σ b) at hab
    change D (π x) (σ y)
    rwa [ha,←hb]
  · intro hxy
    exact ⟨y,⟨x,rfl,hxy⟩,rfl⟩

theorem pullback_image_of_bisaturated (π : A → Q) (σ : B → R)
    (D : A → B → Prop) (hD : Bisaturated π σ D) :
    GroupActions.pullback π σ (image π σ D) = D :=
  (pullback_image π σ D).trans hD

/-- Arbitrary quotient relations correspond to FULL endpoint-saturated old
relations. No quotient section or coherent representative is chosen. -/
def relationEquiv (π : A → Q) (σ : B → R)
    (surjπ : Function.Surjective π) (surjσ : Function.Surjective σ) :
    (Q → R → Prop) ≃ {D : A → B → Prop // Bisaturated π σ D} where
  toFun D := ⟨GroupActions.pullback π σ D,pullback_bisaturated π σ D⟩
  invFun D := image π σ D.val
  left_inv D := image_pullback π σ surjπ surjσ D
  right_inv D := Subtype.ext (pullback_image_of_bisaturated π σ D.val D.property)

theorem pullback_nonempty_iff (π : A → Q) (σ : B → R)
    (surjπ : Function.Surjective π) (surjσ : Function.Surjective σ)
    (D : Q → R → Prop) :
    (∃ a b, GroupActions.pullback π σ D a b) ↔ ∃ q r, D q r := by
  constructor
  · rintro ⟨a,b,h⟩
    exact ⟨π a,σ b,h⟩
  · rintro ⟨q,r,h⟩
    obtain ⟨a,rfl⟩ := surjπ q
    obtain ⟨b,rfl⟩ := surjσ r
    exact ⟨a,b,h⟩

theorem pullback_right_kernel (π : A → Q) (σ : B → R) (D : Q → R → Prop) :
    (fun x z => ∃ y, GroupActions.pullback π σ D x y ∧
      GroupActions.kernel σ y z) = GroupActions.pullback π σ D := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y,hxy,hyz⟩
    change σ y = σ z at hyz
    change D (π x) (σ z)
    exact hyz ▸ hxy
  · exact fun h => ⟨z,h,rfl⟩

theorem pullback_left_kernel (π : A → Q) (σ : B → R) (D : Q → R → Prop) :
    (fun x z => ∃ y, GroupActions.kernel π x y ∧
      GroupActions.pullback π σ D y z) = GroupActions.pullback π σ D := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y,hxy,hyz⟩
    change π x = π y at hxy
    change D (π x) (σ z)
    exact hxy.symm ▸ hyz
  · exact fun h => ⟨x,rfl,h⟩

/-- The full inverse images already absorb the actual middle kernel. -/
theorem pullback_composition_with_kernel (π : A → Q) (σ : B → R) (τ : C → U)
    (surjσ : Function.Surjective σ) (D : Q → R → Prop) (F : R → U → Prop) :
    GroupActions.pullback π τ (fun x z => ∃ y, D x y ∧ F y z) =
      (fun x z => ∃ y, (∃ w, GroupActions.pullback π σ D x w ∧
        GroupActions.kernel σ w y) ∧ GroupActions.pullback σ τ F y z) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨q,hD,hF⟩
    obtain ⟨b,rfl⟩ := surjσ q
    exact ⟨b,⟨b,hD,rfl⟩,hF⟩
  · rintro ⟨y,⟨w,hD,hw⟩,hF⟩
    refine ⟨σ y, ?_, hF⟩
    change σ w = σ y at hw
    exact hw ▸ hD

theorem image_comp (π : A → Q) (σ : B → R) (τ : C → U)
    (surjπ : Function.Surjective π) (surjσ : Function.Surjective σ)
    (surjτ : Function.Surjective τ) (D : A → B → Prop) (F : B → C → Prop)
    (hD : Bisaturated π σ D) (hF : Bisaturated σ τ F) :
    image π τ (fun x z => ∃ y, D x y ∧ F y z) =
      (fun x z => ∃ y, image π σ D x y ∧ image σ τ F y z) := by
  have hp : GroupActions.pullback π τ
      (fun x z => ∃ y, image π σ D x y ∧ image σ τ F y z) =
      (fun x z => ∃ y, D x y ∧ F y z) := by
    rw [ExactCRT.pullback_comp π σ τ surjσ,
      pullback_image_of_bisaturated π σ D hD,
      pullback_image_of_bisaturated σ τ F hF]
  have hh := congrArg (image π τ) hp
  rw [image_pullback π τ surjπ surjτ] at hh
  exact hh.symm

theorem pullback_identity (π : A → Q) :
    GroupActions.pullback π π (fun x y => x = y) = GroupActions.kernel π := rfl

theorem pullback_converse (π : A → Q) (σ : B → R) (D : Q → R → Prop) :
    GroupActions.pullback σ π (fun y x => D x y) =
      (fun y x => GroupActions.pullback π σ D x y) := rfl

theorem pullback_inter (π : A → Q) (σ : B → R) (D F : Q → R → Prop) :
    GroupActions.pullback π σ (fun x y => D x y ∧ F x y) =
      (fun x y => GroupActions.pullback π σ D x y ∧ GroupActions.pullback π σ F x y) := rfl

theorem pullback_all {I : Sort*} (π : A → Q) (σ : B → R) (D : I → Q → R → Prop) :
    GroupActions.pullback π σ (fun x y => ∀ i, D i x y) =
      (fun x y => ∀ i, GroupActions.pullback π σ (D i) x y) := rfl

theorem image_converse (π : A → Q) (σ : B → R) (D : A → B → Prop) :
    image σ π (fun y x => D x y) = (fun y x => image π σ D x y) := by
  funext y x
  apply propext
  constructor <;> rintro ⟨a,b,ha,hb,hab⟩ <;> exact ⟨b,a,hb,ha,hab⟩

theorem image_inter (π : A → Q) (σ : B → R)
    (surjπ : Function.Surjective π) (surjσ : Function.Surjective σ)
    (D F : A → B → Prop) (hD : Bisaturated π σ D) (hF : Bisaturated π σ F) :
    image π σ (fun x y => D x y ∧ F x y) =
      (fun x y => image π σ D x y ∧ image π σ F x y) := by
  have hp : GroupActions.pullback π σ
      (fun x y => image π σ D x y ∧ image π σ F x y) =
      (fun x y => D x y ∧ F x y) := by
    rw [pullback_inter,pullback_image_of_bisaturated π σ D hD,
      pullback_image_of_bisaturated π σ F hF]
  have hh := congrArg (image π σ) hp
  rw [image_pullback π σ surjπ surjσ] at hh
  exact hh.symm

end Relations
end CCO.RigidGroupoid.Geometry.Quotient
