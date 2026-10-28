import CCO.Owners.Product.Matching
import Mathlib.Algebra.Group.Action.Faithful

/-! The nested target lifts the ENTIRE prescribed matching pair. -/
namespace CCO.Owners.Product
variable {GD GC GO GT D C O T : Type*}
variable [Group GD] [Group GC] [Group GO] [Group GT]
variable [MulAction GD D] [MulAction GC C] [MulAction GO O] [MulAction GT T]
variable (ρD : GD →* GO) (ρC : GC →* GO) (τ : GD →* GT) (ρT : GT →* GO)
variable (πD : D → O) (πC : C → O) (t : D → T) (s : T → O)
variable (eqD : ∀ g x, πD (g • x) = ρD g • πD x)
variable (eqC : ∀ g x, πC (g • x) = ρC g • πC x)
variable (eqT : ∀ g x, t (g • x) = τ g • t x)
variable (eqS : ∀ η x, s (η • x) = ρT η • s x)
variable (factor : ∀ x, πD x = s (t x))

/-- Induced owner components agree because O is the actual faithful
permutation action. No section or separately chosen owner action is added. -/
theorem nested_owner_component (eqD : ∀ g x, πD (g • x) = ρD g • πD x)
    (eqT : ∀ g x, t (g • x) = τ g • t x)
    (eqS : ∀ η x, s (η • x) = ρT η • s x)
    (factor : ∀ x, πD x = s (t x)) [FaithfulSMul GO O] (surjD : Function.Surjective πD)
    (g : GD) : ρT (τ g) = ρD g := by
  apply eq_of_smul_eq_smul (α := O)
  intro o
  obtain ⟨d,rfl⟩ := surjD o
  calc
    ρT (τ g) • πD d = s (τ g • t d) := by rw [factor,eqS]
    _ = s (t (g • d)) := congrArg s (eqT g d).symm
    _ = πD (g • d) := (factor _).symm
    _ = ρD g • πD d := eqD g d

/-- A group-component formulation, later discharged by factorization. -/
def nestedTarget (compat : ∀ g, ρT (τ g) = ρD g) :
    Matching ρD ρC →* Matching ρT ρC where
  toFun g := ⟨(τ g.val.1,g.val.2),(compat _).trans g.property⟩
  map_one' := by apply Subtype.ext; exact Prod.ext τ.map_one rfl
  map_mul' g h := by apply Subtype.ext; exact Prod.ext (τ.map_mul _ _) rfl

def nestedProjection (w : Pullback πD πC) : Pullback s πC :=
  ⟨(t w.val.1,w.val.2),(factor _).symm.trans w.property⟩

theorem nestedProjection_surjective (surjT : Function.Surjective t) :
    Function.Surjective (nestedProjection πD πC t s factor) := by
  rintro ⟨⟨u,c⟩,huc⟩
  obtain ⟨d,rfl⟩ := surjT u
  exact ⟨⟨(d,c),(factor _).trans huc⟩,rfl⟩

/-- The nested argument does NOT use C's prescribed-point premise. -/
theorem prescribed_nested (compat : ∀ g, ρT (τ g) = ρD g)
    (liftD : GroupActions.PrescribedLift τ t) :
    letI := pullbackAction ρD ρC πD πC eqD eqC
    letI := pullbackAction ρT ρC s πC eqS eqC
    GroupActions.PrescribedLift (nestedTarget ρD ρC τ ρT compat)
      (nestedProjection πD πC t s factor) := by
  letI := pullbackAction ρD ρC πD πC eqD eqC
  letI := pullbackAction ρT ρC s πC eqS eqC
  intro w w' α hα
  have ht : α.val.1 • t w.val.1 = t w'.val.1 := congrArg (fun z => z.val.1) hα
  have hc : α.val.2 • w.val.2 = w'.val.2 := congrArg (fun z => z.val.2) hα
  obtain ⟨g,hg,hgw⟩ := liftD w.val.1 w'.val.1 α.val.1 ht
  have hgC : ρD g = ρC α.val.2 := (compat g).symm.trans (by rw [hg]; exact α.property)
  refine ⟨⟨(g,α.val.2),hgC⟩,?_,?_⟩
  · apply Subtype.ext; exact Prod.ext hg rfl
  · apply Subtype.ext; exact Prod.ext hgw hc

theorem onto_and_kernel_nested
    (eqT : ∀ g x, t (g • x) = τ g • t x)
    (eqS : ∀ η x, s (η • x) = ρT η • s x) [Nonempty (Pullback πD πC)]
    (surjT : Function.Surjective t) (compat : ∀ g, ρT (τ g) = ρD g)
    (liftD : GroupActions.PrescribedLift τ t) :
    letI := pullbackAction ρD ρC πD πC eqD eqC
    letI := pullbackAction ρT ρC s πC eqS eqC
    Function.Surjective (nestedTarget ρD ρC τ ρT compat) ∧
      GroupActions.FibreTransitive (nestedTarget ρD ρC τ ρT compat)
        (nestedProjection πD πC t s factor) := by
  letI := pullbackAction ρD ρC πD πC eqD eqC
  letI := pullbackAction ρT ρC s πC eqS eqC
  apply (GroupActions.prescribed_action_point_lifting _ _
    (nestedProjection_surjective πD πC t s factor surjT) ?_).mpr
  · exact prescribed_nested ρD ρC τ ρT πD πC t s eqD eqC eqS factor compat liftD
  · intro g w
    apply Subtype.ext
    exact Prod.ext (eqT _ _) rfl

end CCO.Owners.Product
