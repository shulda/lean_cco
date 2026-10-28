import CCO.Owners.Product.Controls.Fullness
import CCO.GroupActions
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.TypeTags.Finite

/-! A literal finite matching-pair ACTION countercontrol. The C action below
is the stated proper subgroup, and is never passed off as the full group of
its difference structure. Onto owner actions alone do not give point lifts. -/
namespace CCO.Owners.Product.Controls.MissingPoint
open Fullness

abbrev GD := Multiplicative Factor
abbrev GC := Multiplicative Bit
abbrev GO := Multiplicative Bit
abbrev GT := Multiplicative Bit

@[instance_reducible] def dAction : MulAction GD Factor where
  smul g x := g.toAdd+x
  one_smul x := zero_add x
  mul_smul g h x := add_assoc g.toAdd h.toAdd x

@[instance_reducible] def cAction : MulAction GC Factor where
  smul g x := (g.toAdd+x.1,x.2)
  one_smul x := by exact Prod.ext (zero_add x.1) rfl
  mul_smul g h x := by exact Prod.ext (add_assoc g.toAdd h.toAdd x.1) rfl

@[instance_reducible] def bitAction : MulAction GO Bit where
  smul g x := g.toAdd+x
  one_smul x := zero_add x
  mul_smul g h x := add_assoc g.toAdd h.toAdd x

local instance : MulAction GD Factor := dAction
local instance : MulAction GC Factor := cAction
local instance : MulAction GO Bit := bitAction
local instance : SMul GD Factor := dAction.toSMul
local instance : SMul GC Factor := cAction.toSMul
local instance : SMul GO Bit := bitAction.toSMul

def rhoD : GD →* GO where
  toFun g := Multiplicative.ofAdd g.toAdd.1
  map_one' := rfl
  map_mul' _ _ := rfl

def rhoC : GC →* GO := MonoidHom.id _

def tau : GD →* GT where
  toFun g := Multiplicative.ofAdd g.toAdd.2
  map_one' := rfl
  map_mul' _ _ := rfl

def dOwner (x : Factor) : Bit := x.1
def cOwner (x : Factor) : Bit := x.1
def dTarget (x : Factor) : Bit := x.2

theorem dOwner_equivariant (g : GD) (x : Factor) :
    dOwner (g • x) = rhoD g • dOwner x := rfl

theorem cOwner_equivariant (g : GC) (x : Factor) :
    cOwner (g • x) = rhoC g • cOwner x := rfl

theorem dTarget_equivariant (g : GD) (x : Factor) :
    dTarget (g • x) = tau g • dTarget x := rfl

theorem dOwner_surjective : Function.Surjective dOwner := by decide

theorem cOwner_surjective : Function.Surjective cOwner := by decide

theorem dTarget_surjective : Function.Surjective dTarget := by decide

theorem d_prescribed_point : GroupActions.PrescribedLift tau dTarget := by
  unfold GroupActions.PrescribedLift
  decide

theorem d_onto_kernel : Function.Surjective tau ∧ GroupActions.FibreTransitive tau dTarget :=
  (GroupActions.prescribed_action_point_lifting tau dTarget
    dTarget_surjective dTarget_equivariant).mpr d_prescribed_point

theorem c_owner_onto : Function.Surjective rhoC := Function.surjective_id

theorem c_missing_point : ¬ GroupActions.PrescribedLift rhoC cOwner := by
  intro h
  obtain ⟨g,_,hg⟩ := h (0,0) (0,1) 1 rfl
  have hc := congrArg Prod.snd hg
  exact (by decide : (0 : Bit) ≠ 1) hc

/-- Exactly the pairs whose entire O-components match. -/
def matchingGroup : Subgroup (GD × GC) where
  carrier := {g | rhoD g.1 = rhoC g.2}
  one_mem' := rfl
  mul_mem' := by
    rintro g h hg hh
    change rhoD g.1 = rhoC g.2 at hg
    change rhoD h.1 = rhoC h.2 at hh
    change rhoD (g.1*h.1) = rhoC (g.2*h.2)
    rw [map_mul,map_mul,hg,hh]
  inv_mem' := by
    rintro g hg
    change rhoD g.1 = rhoC g.2 at hg
    change rhoD g.1⁻¹ = rhoC g.2⁻¹
    rw [map_inv,map_inv,hg]

abbrev Matching := ↥matchingGroup

@[instance_reducible] def fullAction : MulAction Matching Point where
  smul g x := (g.val.1.toAdd.1+x.1,g.val.1.toAdd.2+x.2.1,x.2.2)
  one_smul x := by
    exact Prod.ext (zero_add x.1) (Prod.ext (zero_add x.2.1) rfl)
  mul_smul g h x := by
    exact Prod.ext (add_assoc _ _ _) (Prod.ext (add_assoc _ _ _) rfl)

local instance : MulAction Matching Point := fullAction
local instance : SMul Matching Point := fullAction.toSMul

theorem full_D_coordinate (g : Matching) (x : Point) :
    pD (g • x) = g.val.1 • pD x := rfl

theorem full_C_coordinate (g : Matching) (x : Point) :
    pC (g • x) = g.val.2 • pC x := by
  have hg := congrArg Multiplicative.toAdd g.property
  change g.val.1.toAdd.1 = g.val.2.toAdd at hg
  change (g.val.1.toAdd.1+x.1,x.2.2) = (g.val.2.toAdd+x.1,x.2.2)
  rw [hg]

def fullTarget : Matching →* GT where
  toFun g := tau g.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

def pointTarget (x : Point) : Bit := x.2.1

theorem fullTarget_equivariant (g : Matching) (x : Point) :
    pointTarget (g • x) = fullTarget g • pointTarget x := rfl

/-- The matching-pair action really is onto the ENTIRE T group. -/
theorem fullTarget_onto : Function.Surjective fullTarget := by
  intro g
  exact ⟨⟨(Multiplicative.ofAdd (0,g.toAdd),1),rfl⟩,rfl⟩

theorem pointTarget_onto : Function.Surjective pointTarget := by decide

theorem last_bit_fixed (g : Matching) (x : Point) :
    (g • x : Point).2.2 = x.2.2 := rfl

/-- Even the whole matching group cannot change this C bit, hence its
T-kernel cannot be transitive on this genuine fibre. -/
theorem fullTarget_kernel_not_transitive :
    ¬ GroupActions.FibreTransitive fullTarget pointTarget := by
  intro h
  obtain ⟨g,_,hg⟩ := h (0,0,0) (0,0,1) rfl
  have hc := congrArg (fun x : Point => x.2.2) hg
  exact (by decide : (0 : Bit) ≠ 1) hc

theorem complete_control :
    (Function.Surjective tau ∧ GroupActions.FibreTransitive tau dTarget) ∧
    Function.Surjective rhoC ∧ Function.Surjective fullTarget ∧
    ¬ GroupActions.PrescribedLift rhoC cOwner ∧
    ¬ GroupActions.FibreTransitive fullTarget pointTarget :=
  ⟨d_onto_kernel,c_owner_onto,fullTarget_onto,c_missing_point,fullTarget_kernel_not_transitive⟩

end CCO.Owners.Product.Controls.MissingPoint
