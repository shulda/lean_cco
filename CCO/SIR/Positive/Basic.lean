import CCO.ActionBridge
import Mathlib.Data.Finset.Image

/-! Finite-set SIR axioms. Parameters are fixed pointwise, and stationarity
extends a prescribed map, represented by any ambient extension of that map. -/
universe u v w t
namespace CCO.SIR.Positive
variable {P : Type*} {G : Type*} [Group G] [MulAction G P] [DecidableEq P]

def transport (g : G) (A : Finset P) : Finset P :=
  A.map (MulAction.toPerm g).toEmbedding

@[simp] theorem mem_transport (g : G) (A : Finset P) (x : P) :
    x ∈ transport g A ↔ ∃ a ∈ A, g • a = x := by
  change x ∈ A.map (MulAction.toPerm g).toEmbedding ↔ _
  exact Finset.mem_map

@[simp] theorem smul_mem_transport (g : G) (A : Finset P) (x : P) :
    g • x ∈ transport g A ↔ x ∈ A := by
  rw [mem_transport]
  constructor
  · rintro ⟨a,ha,h⟩
    exact (MulAction.injective g h) ▸ ha
  · exact fun h => ⟨x,h,rfl⟩

@[simp] theorem transport_union (g : G) (A B : Finset P) :
    transport g (A ∪ B) = transport g A ∪ transport g B := by
  classical
  exact Finset.map_union _ _

@[simp] theorem transport_inv (g : G) (A : Finset P) :
    transport g⁻¹ (transport g A) = A := by
  classical
  ext x
  simp only [mem_transport]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,h⟩
    have hh : a = x := (inv_smul_smul g a).symm.trans h
    exact hh ▸ ha
  · intro hx
    exact ⟨g • x,⟨x,hx,rfl⟩,inv_smul_smul g x⟩

/-- A real finite-set stationary independence relation, including empty
bases, both transitivity directions, and pointwise stationarity for every
prescribed finite map. The latter is represented by an arbitrary ambient
automorphism extending that map; homogeneity provides such an extension. -/
structure StationaryIndependence
    (I : Finset P → Finset P → Finset P → Prop) : Prop where
  normalization : ∀ A B C, I (A ∪ C) C (B ∪ C) ↔ I A C B
  invariance : ∀ (g : G) A B C,
    I (transport g A) (transport g C) (transport g B) ↔ I A C B
  symmetry : ∀ A B C, I A C B ↔ I B C A
  restriction : ∀ A B C A' B', A' ⊆ A → B' ⊆ B → I A C B → I A' C B'
  transitivity : ∀ A B C D, I A C (B ∪ D) ↔ I A C B ∧ I A (B ∪ C) D
  existence : ∀ A B C, ∃ g : G,
    (∀ c ∈ C, g • c = c) ∧ I (transport g A) C B
  stationarity : ∀ A B C (g : G), (∀ c ∈ C, g • c = c) →
    I A C B → I (transport g A) C B → ∃ h : G,
      (∀ b ∈ B ∪ C, h • b = b) ∧ ∀ a ∈ A, h • a = g • a

end CCO.SIR.Positive
