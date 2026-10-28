import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic.FinCases

/-! A genuine subgroup of an elementary abelian 2-module is a genuine
F2-subspace. No additional linearity of intrinsic/local/actual groups is
assumed. These bridges retain the actual group representations explicitly. -/

universe u v z
namespace CCO.FiniteKernel
abbrev F2 := ZMod 2

namespace F2Subgroup
variable {V : Type u} [AddCommGroup V] [Module F2 V]

def toSubmodule (H : Subgroup (Multiplicative V)) : Submodule F2 V where
  carrier := {x | Multiplicative.ofAdd x ∈ H}
  zero_mem' := H.one_mem
  add_mem' hx hy := H.mul_mem hx hy
  smul_mem' a x hx := by
    change Multiplicative.ofAdd x ∈ H at hx
    fin_cases a
    · change Multiplicative.ofAdd ((0 : F2) • x) ∈ H
      rw [zero_smul]
      exact H.one_mem
    · change Multiplicative.ofAdd ((1 : F2) • x) ∈ H
      simpa only [one_smul] using hx

def ofSubmodule (W : Submodule F2 V) : Subgroup (Multiplicative V) where
  carrier := {x | Multiplicative.toAdd x ∈ W}
  one_mem' := W.zero_mem
  mul_mem' hx hy := W.add_mem hx hy
  inv_mem' hx := W.neg_mem hx

@[simp] theorem mem_toSubmodule (H : Subgroup (Multiplicative V)) (x : V) :
    x ∈ toSubmodule H ↔ Multiplicative.ofAdd x ∈ H := Iff.rfl

@[simp] theorem mem_ofSubmodule (W : Submodule F2 V) (x : Multiplicative V) :
    x ∈ ofSubmodule W ↔ Multiplicative.toAdd x ∈ W := Iff.rfl

@[simp] theorem of_to (H : Subgroup (Multiplicative V)) :
    ofSubmodule (toSubmodule H) = H := by ext x; rfl

@[simp] theorem to_of (W : Submodule F2 V) :
    toSubmodule (ofSubmodule W) = W := by ext x; rfl

def linearPreimage {G : Type v} [Group G]
    (f : Multiplicative V →* G) (H : Subgroup G) : Submodule F2 V :=
  toSubmodule (H.comap f)

def pairRepresentation {W : Type v} [AddCommGroup W]
    {G : Type*} {H : Type*} [Group G] [Group H]
    (e : Multiplicative V ≃* G) (f : Multiplicative W ≃* H) :
    Multiplicative (V × W) ≃* (G × H) where
  toFun x := (e (Multiplicative.ofAdd (Multiplicative.toAdd x).1),
    f (Multiplicative.ofAdd (Multiplicative.toAdd x).2))
  invFun x := Multiplicative.ofAdd (Multiplicative.toAdd (e.symm x.1),Multiplicative.toAdd (f.symm x.2))
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by
    apply Prod.ext
    · exact e.map_mul _ _
    · exact f.map_mul _ _

def tupleRepresentation {I : Type z} {V : I → Type u} [∀ i,AddCommGroup (V i)]
    {G : I → Type v} [∀ i,Group (G i)] (e : ∀ i,Multiplicative (V i) ≃* G i) :
    Multiplicative (∀ i,V i) ≃* (∀ i,G i) where
  toFun x i := e i (Multiplicative.ofAdd (Multiplicative.toAdd x i))
  invFun x := Multiplicative.ofAdd (fun i => Multiplicative.toAdd ((e i).symm (x i)))
  left_inv x := by funext i; exact (e i).symm_apply_apply (Multiplicative.ofAdd (Multiplicative.toAdd x i))
  right_inv x := by funext i; exact (e i).apply_symm_apply (x i)
  map_mul' x y := by funext i; exact (e i).map_mul _ _

end F2Subgroup
end CCO.FiniteKernel
