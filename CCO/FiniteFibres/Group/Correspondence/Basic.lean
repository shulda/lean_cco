import Mathlib.Data.Setoid.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Data.Fintype.Powerset

/-! C21–C22: ALL invariant equivalences in an arbitrary transitive action.
The acting group may be infinite or nonfaithful; no CCO or group-order
theorem is used. Coset projections below are actual left-coset projections,
with their independence and equivariance proved from stabilizer containment. -/

universe u v
namespace CCO.FiniteFibres.Group.Correspondence

variable (G : Type u) [Group G] (A : Type v) [MulAction G A]

abbrev InvEq := {E : Setoid A // ∀ g : G, ∀ x y, E x y → E (g • x) (g • y)}

namespace InvEq
variable {G A}

instance : CoeFun (InvEq G A) (fun _ => A → A → Prop) := ⟨fun E => E.val.r⟩
instance : PartialOrder (InvEq G A) := inferInstanceAs (PartialOrder {E : Setoid A // _})

@[ext] theorem ext {E F : InvEq G A} (h : ∀ x y, E x y ↔ F x y) : E = F :=
  Subtype.ext (Setoid.ext h)

def meet (s : Set (InvEq G A)) : InvEq G A :=
  ⟨{ r := fun x y => ∀ E ∈ s, E x y
     iseqv := ⟨fun x E _ => E.val.refl x,
       fun h E hE => E.val.symm (h E hE),
       fun h h' E hE => E.val.trans (h E hE) (h' E hE)⟩ },
   fun g x y h E hE => E.property g x y (h E hE)⟩

instance : InfSet (InvEq G A) := ⟨meet⟩
instance : CompleteLattice (InvEq G A) := completeLatticeOfInf (InvEq G A) fun s =>
  ⟨fun E hE _ _ h => h E hE,fun _ h _ _ hxy E hE => h hE hxy⟩

@[simp] theorem top_apply (x y : A) : (⊤ : InvEq G A) x y ↔ True := by
  change (∀ E ∈ (∅ : Set (InvEq G A)),E x y) ↔ True
  simp

@[simp] theorem bot_apply (x y : A) : (⊥ : InvEq G A) x y ↔ x = y := by
  constructor
  · intro h
    let D : InvEq G A := ⟨⊥,fun _ _ _ h => by cases h; rfl⟩
    exact (show (⊥ : InvEq G A) ≤ D from bot_le) h
  · rintro rfl
    exact (⊥ : InvEq G A).val.refl x

instance [Finite A] : Finite (InvEq G A) := by
  classical
  letI := Fintype.ofFinite A
  apply Finite.of_injective (f := fun E : InvEq G A => {p : A × A | E p.1 p.2})
  intro E F h
  apply InvEq.ext
  intro x y
  exact Set.ext_iff.mp h (x,y)

theorem move_iff (E : InvEq G A) (g : G) (x y : A) :
    E (g • x) (g • y) ↔ E x y := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using E.property g⁻¹ (g • x) (g • y) h
  · exact E.property g x y

/-- C21: the subgroup of motions preserving the base E-class. -/
def subgroup (E : InvEq G A) (a : A) : Subgroup G where
  carrier := {g | E (g • a) a}
  one_mem' := by
    change E ((1 : G) • a) a
    simpa only [one_smul] using E.val.refl a
  mul_mem' := by
    intro g h hg hh
    change E ((g*h) • a) a
    rw [mul_smul]
    exact E.val.trans (E.property g (h • a) a hh) hg
  inv_mem' := by
    intro g hg
    have h := E.property g⁻¹ (g • a) a hg
    exact E.val.symm (by simpa only [inv_smul_smul] using h)

theorem stabilizer_le (E : InvEq G A) (a : A) : MulAction.stabilizer G a ≤ E.subgroup a := by
  intro g hg
  change E (g • a) a
  change g • a = a at hg
  simpa only [hg] using E.val.refl a

theorem relative_motion_iff (E : InvEq G A) (a : A) (g h : G) :
    g⁻¹*h ∈ E.subgroup a ↔ E (g • a) (h • a) := by
  constructor
  · intro hmem
    change E ((g⁻¹*h) • a) a at hmem
    have ht := E.property g ((g⁻¹*h) • a) a hmem
    have hs : g • ((g⁻¹*h) • a) = h • a := by rw [smul_smul,mul_inv_cancel_left]
    exact E.val.symm (hs ▸ ht)
  · intro hrel
    change E ((g⁻¹*h) • a) a
    have ht := E.property g⁻¹ (g • a) (h • a) hrel
    exact E.val.symm (by simpa only [inv_smul_smul,mul_smul] using ht)

end InvEq

variable {G A}
variable (trans : ∀ x y : A, ∃ g : G, g • x = y) (a : A)

noncomputable def representative (x : A) : G := (trans a x).choose

theorem representative_spec (x : A) : representative (G := G) trans a x • a = x :=
  (trans a x).choose_spec

noncomputable def projection (H : Subgroup G) (_hH : MulAction.stabilizer G a ≤ H)
    (x : A) : G ⧸ H := QuotientGroup.mk (representative (G := G) trans a x)

theorem projection_move (H : Subgroup G) (hH : MulAction.stabilizer G a ≤ H)
    (g : G) (x : A) :
    projection trans a H hH (g • x) = g • projection trans a H hH x := by
  apply QuotientGroup.eq.mpr
  apply hH
  change ((representative (G := G) trans a (g • x))⁻¹ * (g * representative (G := G) trans a x)) • a = a
  calc
    _ = (representative (G := G) trans a (g • x))⁻¹ • (g • x) := by
      rw [mul_smul,mul_smul,representative_spec]
    _ = (representative (G := G) trans a (g • x))⁻¹ •
        (representative (G := G) trans a (g • x) • a) :=
      congrArg (fun z => (representative (G := G) trans a (g • x))⁻¹ • z)
        (representative_spec trans a (g • x)).symm
    _ = a := inv_smul_smul _ _

theorem projection_base (H : Subgroup G) (hH : MulAction.stabilizer G a ≤ H) :
    projection trans a H hH a = QuotientGroup.mk (1 : G) := by
  apply QuotientGroup.eq.mpr
  change (representative (G := G) trans a a)⁻¹ * 1 ∈ H
  rw [mul_one]
  apply H.inv_mem
  exact hH (representative_spec trans a a)

theorem projection_orbit (H : Subgroup G) (hH : MulAction.stabilizer G a ≤ H) (g : G) :
    projection trans a H hH (g • a) = (g : G ⧸ H) := by
  rw [projection_move,projection_base]
  change ((g*1 : G) : G ⧸ H) = (g : G ⧸ H)
  rw [mul_one]

/-- The inverse construction takes the literal kernel of the actual coset
projection. No normality or faithfulness is presumed. -/
noncomputable def ofSubgroup (H : Subgroup G) (hH : MulAction.stabilizer G a ≤ H) : InvEq G A :=
  ⟨Setoid.ker (projection trans a H hH),fun g x y hxy => by
    change projection trans a H hH (g • x) = projection trans a H hH (g • y)
    rw [projection_move,projection_move,hxy]⟩

theorem subgroup_ofSubgroup (H : Subgroup G) (hH : MulAction.stabilizer G a ≤ H) :
    (ofSubgroup trans a H hH).subgroup a = H := by
  ext g
  change projection trans a H hH (g • a) = projection trans a H hH a ↔ g ∈ H
  rw [projection_orbit,projection_base,QuotientGroup.eq]
  simp only [mul_one,H.inv_mem_iff]

theorem ofSubgroup_subgroup (E : InvEq G A) :
    ofSubgroup trans a (E.subgroup a) (E.stabilizer_le a) = E := by
  apply InvEq.ext
  intro x y
  change (representative (G := G) trans a x : G ⧸ E.subgroup a) =
    (representative (G := G) trans a y : G ⧸ E.subgroup a) ↔ E x y
  rw [QuotientGroup.eq,InvEq.relative_motion_iff,representative_spec,representative_spec]

include trans in
theorem subgroup_le_iff (E F : InvEq G A) : E.subgroup a ≤ F.subgroup a ↔ E ≤ F := by
  constructor
  · intro h x y hxy
    have hE := (E.relative_motion_iff a (representative (G := G) trans a x) (representative (G := G) trans a y)).mpr
      (by simpa only [representative_spec] using hxy)
    have hF := (F.relative_motion_iff a (representative (G := G) trans a x) (representative (G := G) trans a y)).mp (h hE)
    simpa only [representative_spec] using hF
  · intro h g hg
    exact h hg

/-- C22: the FULL invariant-equivalence poset, with every subgroup above
the actual point stabilizer. The acting group is completely unrestricted. -/
noncomputable def subgroupCorrespondence : InvEq G A ≃o Set.Ici (MulAction.stabilizer G a) where
  toFun E := ⟨E.subgroup a,E.stabilizer_le a⟩
  invFun H := ofSubgroup trans a H.val H.property
  left_inv := ofSubgroup_subgroup trans a
  right_inv H := Subtype.ext (subgroup_ofSubgroup trans a H.val H.property)
  map_rel_iff' := fun {E F} => subgroup_le_iff trans a E F

end CCO.FiniteFibres.Group.Correspondence
