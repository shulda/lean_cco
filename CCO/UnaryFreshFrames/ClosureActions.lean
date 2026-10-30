import CCO.UnaryFreshFrames.Language
import CCO.AclOwners.Avoidance
import Mathlib.Data.Set.Finite.Lattice

/-! B039 C01–C03: actual unary closure, pointwise stabilisers and orbit acl.
The abstract finite-avoidance theorem imported here is the accepted B010 API. -/
universe u v w
namespace CCO.UnaryFreshFrames

variable (G : Type w) {V : Type v} [Group G] [MulAction G V]

def fixer (A : Set V) : Subgroup G where
  carrier := {g | ∀ x ∈ A, g • x = x}
  one_mem' := fun _ _ => one_smul _ _
  mul_mem' := by
    intro g h hg hh x hx
    rw [mul_smul, hh x hx, hg x hx]
  inv_mem' := by
    intro g hg x hx
    rw [inv_smul_eq_iff, hg x hx]

def orbitOver (A : Set V) (x : V) : Set V := MulAction.orbit (fixer G A) x
def Acl (A : Set V) : Set V := {x | (orbitOver G A x).Finite}
def Dcl (A : Set V) : Set V := {x | ∀ g : fixer G A, g • x = x}

theorem mem_orbitOver_iff {A : Set V} {x y : V} :
    y ∈ orbitOver G A x ↔ ∃ g : G, (∀ a ∈ A, g • a = a) ∧ g • x = y := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, g.property, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem orbitOver_anti {A B : Set V} (h : A ⊆ B) (x : V) :
    orbitOver G B x ⊆ orbitOver G A x := by
  rintro y ⟨g, rfl⟩
  exact ⟨⟨g.val, fun a ha => g.property a (h ha)⟩, rfl⟩

theorem dcl_subset_acl (A : Set V) : Dcl G A ⊆ Acl G A := by
  intro x hx
  exact (Set.finite_singleton x).subset (by
    rintro y ⟨g, rfl⟩
    exact hx g)

namespace Structure
variable {L : Language.{u}} (H : Structure L V)

def LocallyFinite : Prop := ∀ A : Set V, A.Finite → (H.closure A).Finite

theorem locallyFinite_of_singletons (h : ∀ x, (H.closureAt x).Finite) :
    H.LocallyFinite := by
  intro A hA
  have hf : (⋃ x ∈ A, H.closureAt x).Finite := hA.biUnion (fun x _ => h x)
  apply hf.subset
  intro y hy
  obtain ⟨x, hx, hxy⟩ := H.mem_closure_iff_singleton.mp hy
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hxy⟩⟩

theorem aut_mem_closure (g : H.Aut) {A : Set V} {y : V} (hy : y ∈ H.closure A) :
    g • y ∈ H.closure ((fun x => g • x) '' A) := by
  rcases hy with ⟨x, hx, j, t, rfl⟩
  refine ⟨g • x, ⟨x, hx, rfl⟩, ?_⟩
  rw [H.aut_sort g x]
  exact ⟨j, t, (H.aut_eval g t x).symm⟩

theorem aut_closure (g : H.Aut) (A : Set V) :
    H.closure ((fun x => g • x) '' A) = (fun x => g • x) '' H.closure A := by
  apply Set.Subset.antisymm
  · intro y hy
    have hi := H.aut_mem_closure g⁻¹ hy
    have he : (fun x => g⁻¹ • x) '' ((fun x => g • x) '' A) = A := by
      ext x
      simp only [Set.mem_image]
      constructor
      · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
        simpa only [inv_smul_smul] using ha
      · intro hx
        exact ⟨g • x, ⟨x, hx, rfl⟩, inv_smul_smul g x⟩
    rw [he] at hi
    exact ⟨g⁻¹ • y, hi, smul_inv_smul g y⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact H.aut_mem_closure g hx

theorem aut_closed_image (g : H.Aut) {A : Set V} (hA : H.Closed A) :
    H.Closed ((fun x => g • x) '' A) := by
  rintro F _ ⟨x, hx, rfl⟩
  exact ⟨H.func F x, hA F x hx, H.aut_func g F x⟩

theorem closure_fixed (g : H.Aut) {A : Set V}
    (hg : ∀ x ∈ A, g • x = x) : ∀ y ∈ H.closure A, g • y = y := by
  rintro y ⟨x, hx, j, t, rfl⟩
  rw [H.aut_eval, hg x hx]

theorem fixer_closure_eq (G : Subgroup H.Aut) (A : Set V) :
    fixer G (H.closure A) = fixer G A := by
  ext g
  constructor
  · intro hg x hx
    exact hg x (H.subset_closure A hx)
  · intro hg
    exact H.closure_fixed g.val hg

theorem orbitOver_closure_eq (G : Subgroup H.Aut) (A : Set V) (x : V) :
    orbitOver G (H.closure A) x = orbitOver G A x := by
  unfold orbitOver
  rw [H.fixer_closure_eq]

theorem closure_subset_dcl (G : Subgroup H.Aut) (A : Set V) :
    H.closure A ⊆ Dcl G A := by
  intro y hy g
  exact H.closure_fixed g.val.val g.property y hy

def InfiniteClosedOrbits (G : Type w) [Group G] [MulAction G V] : Prop :=
  ∀ (A : Set V), A.Finite → H.Closed A → ∀ x, x ∉ A → (orbitOver G A x).Infinite

theorem acl_eq_closure (G : Subgroup H.Aut) (hfin : H.LocallyFinite)
    (hInf : H.InfiniteClosedOrbits G) {A : Set V} (hA : A.Finite) :
    Acl G A = H.closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hnot
    have hi := hInf (H.closure A) (hfin A hA) (H.closure_closed A) x hnot
    rw [H.orbitOver_closure_eq] at hi
    exact hi hx
  · exact (H.closure_subset_dcl G A).trans (dcl_subset_acl G A)

theorem dcl_eq_closure (G : Subgroup H.Aut) (hfin : H.LocallyFinite)
    (hInf : H.InfiniteClosedOrbits G) {A : Set V} (hA : A.Finite) :
    Dcl G A = H.closure A := by
  apply Set.Subset.antisymm
  · exact (dcl_subset_acl G A).trans (by rw [H.acl_eq_closure G hfin hInf hA])
  · exact H.closure_subset_dcl G A

end Structure
end CCO.UnaryFreshFrames
