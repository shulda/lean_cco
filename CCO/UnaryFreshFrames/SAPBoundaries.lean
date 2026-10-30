import CCO.UnaryFreshFrames.SAPCopies
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fin.Basic

/-! C07/C50: actual full-group SAP does not control arbitrary subgroup
orbits, and the named unary/no-constant assumptions protect this proof. -/
namespace CCO.UnaryFreshFrames.Structure.SAPBoundaries

open CCO.UnaryFreshFrames

/-- The language of one pure sort: no functions and no relations. -/
def pureLanguage : Language where
  Sorts := Unit
  Func := Empty
  Rel := Empty
  input F := nomatch F
  output F := nomatch F
  arity R := nomatch R
  argument R := nomatch R

def pureNat : Structure pureLanguage ℕ where
  sort _ := ()
  func F := nomatch F
  func_sort F := nomatch F
  func_offsort F := nomatch F
  rel R := nomatch R
  rel_sort R := nomatch R

theorem pure_closed (A : Set ℕ) : pureNat.Closed A := fun F => nomatch F

theorem pure_closure (A : Set ℕ) : pureNat.closure A = A :=
  pureNat.closure_eq (pure_closed A)

theorem pure_locallyFinite : pureNat.LocallyFinite := by
  intro A hA
  simpa only [pure_closure] using hA

/-- Every permutation is an ACTUAL full named automorphism here. -/
def pureAut (e : Equiv.Perm ℕ) : pureNat.Aut := by
  refine ⟨e, ⟨fun _ => rfl, ?_, ?_⟩⟩
  · intro F
    exact nomatch F
  · intro R
    exact nomatch R

theorem pure_homogeneous : pureNat.Homogeneous := by
  intro A f g
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f.point g.point f.injective g.injective
  exact ⟨pureAut e, he⟩

/-- Swapping x with any y outside the finite base fixes that whole base.
Thus each off-base FULL orbit contains the infinite complement. -/
theorem pure_infiniteClosedOrbits : pureNat.InfiniteClosedOrbits pureNat.Aut := by
  classical
  intro A hA _ x hx
  have hi : (Set.univ \ A : Set ℕ).Infinite := Set.infinite_univ.sdiff hA
  apply hi.mono
  intro y hy
  apply (mem_orbitOver_iff pureNat.Aut).mpr
  refine ⟨pureAut (Equiv.swap x y), ?_, Equiv.swap_apply_left x y⟩
  intro z hz
  apply Equiv.swap_apply_of_ne_of_ne
  · exact fun he => hx (he ▸ hz)
  · exact fun he => hy.2 (he ▸ hz)

/-- Actual SAP of this countable homogeneous hereditary age, with ALL finite
hidden bases, is proved using the constructed criterion rather than assumed. -/
theorem pure_ageSAP : pureNat.AgeSAP :=
  pureNat.ageSAP_of_infiniteClosedOrbits pure_homogeneous pure_infiniteClosedOrbits

/-- The identity subgroup has singleton stabilizer orbits even off closure. -/
theorem identity_orbit (A : Set ℕ) (x : ℕ) :
    orbitOver (⊥ : Subgroup pureNat.Aut) A x = {x} := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    have he : g.val = 1 := Subsingleton.elim _ _
    change g.val • x = x
    rw [he, one_smul]
  · rintro rfl
    exact ⟨1, one_smul _ _⟩

theorem identity_subgroup_proper : (⊥ : Subgroup pureNat.Aut) ≠ ⊤ := by
  intro h
  have hg : pureAut (Equiv.swap 0 1) ∈ (⊥ : Subgroup pureNat.Aut) := by
    rw [h]
    trivial
  have he := Subgroup.mem_bot.mp hg
  have hp := congrArg (fun a : pureNat.Aut => a • (0 : ℕ)) he
  change Equiv.swap 0 1 0 = 0 at hp
  exact Nat.one_ne_zero ((Equiv.swap_apply_left 0 1).symm.trans hp)

/-- C07: a complete actual SAP model together with a genuinely proper
subgroup whose empty-base orbit is finite outside the empty closure. -/
theorem sap_does_not_give_subgroup_infinitude :
    pureNat.Homogeneous ∧ pureNat.LocallyFinite ∧ pureNat.AgeSAP ∧
      (0 : ℕ) ∉ pureNat.closure ∅ ∧
      (orbitOver (⊥ : Subgroup pureNat.Aut) ∅ 0).Finite ∧
      ¬ pureNat.InfiniteClosedOrbits (⊥ : Subgroup pureNat.Aut) := by
  refine ⟨pure_homogeneous, pure_locallyFinite, pure_ageSAP, ?_, ?_, ?_⟩
  · rw [pure_closure]
    simp
  · rw [identity_orbit]
    exact Set.finite_singleton _
  · intro h
    have hi := h ∅ Set.finite_empty (pure_closed ∅) 0 (by simp)
    rw [identity_orbit] at hi
    exact hi (Set.finite_singleton _)

/-- A zero-ary generator must already belong to every closed set. -/
def NullaryClosed {V : Type*} (c : V) (A : Set V) : Prop := c ∈ A

theorem a_constant_changes_empty_closure : ¬ NullaryClosed false (∅ : Set Bool) := by
  simp [NullaryClosed]

/-- Binary closure genuinely tests pairs, including pairs from opposite
factors. This definition does not silently reuse the unary closure. -/
def BinaryClosed {V : Type*} (f : V → V → V) (A : Set V) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, f x y ∈ A

def mixedValue (x y : Fin 3) : Fin 3 := if x = 0 ∧ y = 1 then 2 else x

/-- C50: two actual binary-closed factors have a nonclosed union. -/
theorem binary_closed_union_failure :
    BinaryClosed mixedValue ({0} : Set (Fin 3)) ∧
      BinaryClosed mixedValue ({1} : Set (Fin 3)) ∧
      ¬ BinaryClosed mixedValue ({0, 1} : Set (Fin 3)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x (rfl : x = 0) y (rfl : y = 0)
    decide
  · rintro x (rfl : x = 1) y (rfl : y = 1)
    decide
  · intro h
    have he := h 0 (by simp) 1 (by simp)
    have hbad : (2 : Fin 3) ∉ ({0, 1} : Set (Fin 3)) := by decide
    exact hbad he

end CCO.UnaryFreshFrames.Structure.SAPBoundaries
