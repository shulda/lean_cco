import CCO.FiniteKernel.BinarySource
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Logic.Equiv.Sigma
import Mathlib.Data.Fintype.Perm

/-! The actual invariant finite-fibre partition covers ALL original points.
Surjectivity makes its labels precisely the nonempty equivalence classes;
the label family is empty exactly when the original universe is empty. -/

universe u v w z
namespace CCO.FiniteKernel

variable {X : Type u} (S : BinaryStructure.{u,v,w} X) (I : Type z)

structure FinitePartition where
  owner : X → I
  surjective : Function.Surjective owner
  finite_fibre : ∀ i, Finite {x : X // owner x = i}
  invariant : ∀ (g : S.Aut) (x y : X),
    owner x = owner y ↔ owner (g.val x) = owner (g.val y)

namespace FinitePartition
variable {S I} (P : FinitePartition S I)

abbrev Fibre (i : I) := {x : X // P.owner x = i}

instance fibreFinite (i : I) : Finite (P.Fibre i) := P.finite_fibre i

theorem fibre_nonempty (i : I) : Nonempty (P.Fibre i) := by
  obtain ⟨x,hx⟩ := P.surjective i
  exact ⟨x,hx⟩

/-- Canonical equivalence between the original entire universe and the disjoint
union of its actual fibres, not a replacement abstract model. -/
def split : X ≃ Sigma P.Fibre where
  toFun x := ⟨P.owner x,⟨x,rfl⟩⟩
  invFun x := x.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨i,x,hx⟩
    dsimp
    cases hx
    rfl

noncomputable def ownerMap (g : S.Aut) (i : I) : I :=
  P.owner (g.val (Classical.choose (P.surjective i)))

theorem ownerMap_apply (g : S.Aut) (x : X) :
    P.ownerMap g (P.owner x) = P.owner (g.val x) := by
  apply (P.invariant g _ x).mp
  exact Classical.choose_spec (P.surjective (P.owner x))

noncomputable def ownerPerm (g : S.Aut) : Equiv.Perm I where
  toFun := P.ownerMap g
  invFun := P.ownerMap g⁻¹
  left_inv := by
    intro i
    obtain ⟨x,rfl⟩ := P.surjective i
    rw [P.ownerMap_apply, P.ownerMap_apply]
    simp
  right_inv := by
    intro i
    obtain ⟨x,rfl⟩ := P.surjective i
    rw [P.ownerMap_apply, P.ownerMap_apply]
    simp

noncomputable def ownerAction : S.Aut →* Equiv.Perm I where
  toFun := P.ownerPerm
  map_one' := by
    ext i
    obtain ⟨x,rfl⟩ := P.surjective i
    exact P.ownerMap_apply 1 x
  map_mul' := by
    intro g h
    ext i
    obtain ⟨x,rfl⟩ := P.surjective i
    change P.ownerMap (g*h) (P.owner x) = P.ownerMap g (P.ownerMap h (P.owner x))
    rw [P.ownerMap_apply, P.ownerMap_apply, P.ownerMap_apply]
    rfl

@[simp] theorem ownerAction_apply (g : S.Aut) (x : X) :
    P.ownerAction g (P.owner x) = P.owner (g.val x) := P.ownerMap_apply g x

noncomputable def kernel : Subgroup S.Aut := P.ownerAction.ker

instance kernel_normal : P.kernel.Normal := by
  dsimp [kernel]
  infer_instance

theorem mem_kernel_iff (g : S.Aut) :
    g ∈ P.kernel ↔ ∀ x, P.owner (g.val x) = P.owner x := by
  change P.ownerAction g = 1 ↔ _
  constructor
  · intro h x
    have hh := congrArg (fun e : Equiv.Perm I => e (P.owner x)) h
    simpa only [P.ownerAction_apply, Equiv.Perm.one_apply] using hh
  · intro h
    ext i
    obtain ⟨x,rfl⟩ := P.surjective i
    exact (P.ownerAction_apply g x).trans (h x)

theorem kernel_fixes (g : P.kernel) (x : X) :
    P.owner (g.val.val x) = P.owner x := (P.mem_kernel_iff g.val).mp g.property x

def fibreStructure (i : I) : BinaryStructure (P.Fibre i) :=
  S.induced {x | P.owner x = i}

abbrev Intrinsic (i : I) := (P.fibreStructure i).Aut

instance intrinsicFinite (i : I) : Finite (P.Intrinsic i) := by
  classical
  letI : Fintype (P.Fibre i) := Fintype.ofFinite _
  change Finite {g : Equiv.Perm (P.Fibre i) // g ∈ (P.fibreStructure i).autGroup}
  infer_instance

end FinitePartition
end CCO.FiniteKernel
