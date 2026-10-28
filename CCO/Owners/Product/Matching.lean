import CCO.GroupActions
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Group.Hom.Defs

/-! The abstract matching-pair action. This file is independent of exact
source geometry and of any fine-colour product theorem. -/
namespace CCO.Owners.Product

variable {GD GC GO GT D C O T : Type*}
variable [Group GD] [Group GC] [Group GO] [Group GT]

def matchingGroup (ρD : GD →* GO) (ρC : GC →* GO) : Subgroup (GD × GC) where
  carrier := {p | ρD p.1 = ρC p.2}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ha hb
    change ρD a.1 = ρC a.2 at ha
    change ρD b.1 = ρC b.2 at hb
    change ρD (a.1*b.1) = ρC (a.2*b.2)
    simp only [map_mul,ha,hb]
  inv_mem' := by
    rintro a ha
    change ρD a.1 = ρC a.2 at ha
    change ρD a.1⁻¹ = ρC a.2⁻¹
    simp only [map_inv,ha]

abbrev Matching (ρD : GD →* GO) (ρC : GC →* GO) := ↥(matchingGroup ρD ρC)

def matchingTarget (ρD : GD →* GO) (ρC : GC →* GO) (τ : GD →* GT) :
    Matching ρD ρC →* GT where
  toFun g := τ g.val.1
  map_one' := τ.map_one
  map_mul' g h := τ.map_mul _ _

abbrev Pullback (πD : D → O) (πC : C → O) := {p : D × C // πD p.1 = πC p.2}

variable [MulAction GD D] [MulAction GC C] [MulAction GO O] [MulAction GT T]
variable (ρD : GD →* GO) (ρC : GC →* GO) (πD : D → O) (πC : C → O)
variable (eqD : ∀ g x, πD (g • x) = ρD g • πD x)
variable (eqC : ∀ g x, πC (g • x) = ρC g • πC x)

@[instance_reducible] def pullbackAction : MulAction (Matching ρD ρC) (Pullback πD πC) where
  smul g w := ⟨(g.val.1 • w.val.1,g.val.2 • w.val.2),by
    rw [eqD,eqC,g.property,w.property]⟩
  one_smul w := by apply Subtype.ext; exact Prod.ext (one_smul _ _) (one_smul _ _)
  mul_smul g h w := by apply Subtype.ext; exact Prod.ext (mul_smul _ _ _) (mul_smul _ _ _)

theorem pullback_fst_surjective (surjC : Function.Surjective πC) :
    Function.Surjective (fun w : Pullback πD πC => w.val.1) := by
  intro d
  obtain ⟨c,hc⟩ := surjC (πD d)
  exact ⟨⟨(d,c),hc.symm⟩,rfl⟩

theorem pullback_snd_surjective (surjD : Function.Surjective πD) :
    Function.Surjective (fun w : Pullback πD πC => w.val.2) := by
  intro c
  obtain ⟨d,hd⟩ := surjD (πC c)
  exact ⟨⟨(d,c),hd⟩,rfl⟩

variable (τ : GD →* GT) (t : D → T)
variable (eqT : ∀ g x, t (g • x) = τ g • t x)

/-- First accept the O-component of the prescribed D-lift, and only then
ask C to realize it. There is no T-to-O map and no section. -/
theorem prescribed_nonnested
    (liftD : GroupActions.PrescribedLift τ t)
    (liftC : GroupActions.PrescribedLift ρC πC) :
    letI := pullbackAction ρD ρC πD πC eqD eqC
    GroupActions.PrescribedLift (matchingTarget ρD ρC τ)
      (fun w : Pullback πD πC => t w.val.1) := by
  letI := pullbackAction ρD ρC πD πC eqD eqC
  intro w w' η hη
  obtain ⟨g,hg,hgw⟩ := liftD w.val.1 w'.val.1 η hη
  have hc : ρD g • πC w.val.2 = πC w'.val.2 := by
    rw [← w.property,← w'.property,← eqD,hgw]
  obtain ⟨h,hh,hhw⟩ := liftC w.val.2 w'.val.2 (ρD g) hc
  refine ⟨⟨(g,h),hh.symm⟩,hg,?_⟩
  apply Subtype.ext
  exact Prod.ext hgw hhw

include eqT
/-- Apply the shared nonempty point criterion only in its valid branch. -/
theorem onto_and_kernel_nonnested [Nonempty (Pullback πD πC)]
    (surjC : Function.Surjective πC) (surjT : Function.Surjective t)
    (liftD : GroupActions.PrescribedLift τ t)
    (liftC : GroupActions.PrescribedLift ρC πC) :
    letI := pullbackAction ρD ρC πD πC eqD eqC
    Function.Surjective (matchingTarget ρD ρC τ) ∧
      GroupActions.FibreTransitive (matchingTarget ρD ρC τ)
        (fun w : Pullback πD πC => t w.val.1) := by
  letI := pullbackAction ρD ρC πD πC eqD eqC
  apply (GroupActions.prescribed_action_point_lifting _ _
    (surjT.comp (pullback_fst_surjective πD πC surjC)) (fun g w => by
      change t (g.val.1 • w.val.1) = τ g.val.1 • t w.val.1
      exact eqT _ _)).mpr
  exact prescribed_nonnested ρD ρC πD πC eqD eqC τ t liftD liftC

end CCO.Owners.Product
