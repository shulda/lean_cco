import CCO.FiniteKernel.ActualMarginals
import CCO.FiniteKernel.ActualPartition
import CCO.FiniteKernel.FiniteContinuation
import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Image

/-! Exact compact-projection quantifiers for the SAME prescribed finite tuple.
Finite families are handled directly. The countable case instantiates the
explicit finite-continuation construction on the genuine local solution levels.
No coherent family or surjective finite restriction is assumed.
-/

universe u v w z
namespace CCO.FiniteKernel.FinitePartition
variable {X : Type u} {S : BinaryStructure.{u,v,w} X} {I : Type z}
variable (P : FinitePartition S I)

def FiniteExtensionProperty (A : Finset I) (g : ∀ i : ↥A, P.Intrinsic i.val) : Prop :=
  ∀ (B : Finset I) (hAB : A ⊆ B), ∃ h : P.solutions B,
    ∀ i : ↥A, h.val ⟨i.val,hAB i.property⟩ = g i

theorem projection_has_finite_extensions (A : Finset I)
    (g : ∀ i : ↥A, P.Intrinsic i.val) (hg : g ∈ Set.range (P.projection A)) :
    P.FiniteExtensionProperty A g := by
  obtain ⟨n,rfl⟩ := hg
  intro B hAB
  exact ⟨⟨P.projection B n,P.projection_solution B n⟩,fun _ => rfl⟩

theorem finite_extension_of_finite_owners [Finite I] (A : Finset I)
    (g : ∀ i : ↥A, P.Intrinsic i.val) (hg : P.FiniteExtensionProperty A g) :
    g ∈ Set.range (P.projection A) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  obtain ⟨h,hh⟩ := hg Finset.univ (Finset.subset_univ A)
  let p : ∀ i, P.Intrinsic i := fun i => h.val ⟨i,Finset.mem_univ i⟩
  have hp : p ∈ P.globalSolutions := fun i j hij =>
    h.property ⟨i,Finset.mem_univ i⟩ ⟨j,Finset.mem_univ j⟩ hij
  refine ⟨P.assembleKernel ⟨p,hp⟩,?_⟩
  funext i
  exact (congrFun (P.rho_assemble ⟨p,hp⟩) i.val).trans (hh i)

/-- C06–08: the exact displayed compact-projection equivalence, with the
explicit finite-failure-bound recursive path supplying sufficiency. -/
theorem compact_projection [Countable I] (A : Finset I)
    (g : ∀ i : ↥A, P.Intrinsic i.val) :
    g ∈ Set.range (P.projection A) ↔ P.FiniteExtensionProperty A g := by
  classical
  constructor
  · exact P.projection_has_finite_extensions A g
  · intro hg
    cases finite_or_infinite I with
    | inl hf =>
      letI := hf
      exact P.finite_extension_of_finite_owners A g hg
    | inr hi =>
      letI := hi
      letI : Nonempty I := Infinite.nonempty I
      obtain ⟨enum,henum⟩ := exists_surjective_nat I
      let E (n : ℕ) : Finset I := A ∪ (Finset.range n).image enum
      have hAE (n : ℕ) : A ⊆ E n := Finset.subset_union_left
      have hE {n m : ℕ} (hnm : n ≤ m) : E n ⊆ E m :=
        Finset.union_subset_union (Finset.Subset.refl _)
          (Finset.image_subset_image (Finset.range_mono hnm))
      let L (n : ℕ) := {h : P.solutions (E n) //
        ∀ i : ↥A, h.val ⟨i.val,hAE n i.property⟩ = g i}
      let restrict (n m : ℕ) (hnm : n ≤ m) (h : L m) : L n :=
        ⟨P.restrictSolutions (hE hnm) h.val,fun i => h.property i⟩
      let T : FiniteTower := {
        Level := L
        finite_level := fun _ => inferInstance
        nonempty_level := by
          intro n
          obtain ⟨h,hh⟩ := hg (E n) (hAE n)
          exact ⟨h,hh⟩
        restrict := restrict
        restrict_self := by
          intro n x
          apply Subtype.ext
          apply Subtype.ext
          funext i
          rfl
        restrict_trans := by
          intro n m k hnm hmk x
          apply Subtype.ext
          apply Subtype.ext
          funext i
          rfl
      }
      obtain ⟨f,hf⟩ := T.coherent_path
      have hcoh := T.coherent_path_restrict f hf
      let idx (i : I) : ℕ := Classical.choose (henum i)
      have hidx (i : I) : enum (idx i) = i := Classical.choose_spec (henum i)
      let stage (i : I) := idx i + 1
      have hstage (i : I) : i ∈ E (stage i) := by
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨idx i,Finset.mem_range.mpr (Nat.lt_succ_self _),hidx i⟩
      let p : ∀ i, P.Intrinsic i := fun i => (f (stage i)).val.val ⟨i,hstage i⟩
      have hpN (i : I) (N : ℕ) (hiN : stage i ≤ N) :
          p i = (f N).val.val ⟨i,hE hiN (hstage i)⟩ := by
        have hc := hcoh (stage i) N hiN
        exact (congrArg (fun h : L (stage i) => h.val.val ⟨i,hstage i⟩) hc).symm
      have hp : p ∈ P.globalSolutions := by
        intro i j hij
        let N := max (stage i) (stage j)
        rw [hpN i N (le_max_left _ _),hpN j N (le_max_right _ _)]
        exact (f N).val.property _ _ hij
      refine ⟨P.assembleKernel ⟨p,hp⟩,?_⟩
      funext i
      exact (congrFun (P.rho_assemble ⟨p,hp⟩) i.val).trans ((f (stage i.val)).property i)

theorem finite_obstruction [Countable I] (A : Finset I)
    (g : ∀ i : ↥A, P.Intrinsic i.val) (hg : g ∉ Set.range (P.projection A)) :
    ∃ (B : Finset I) (hAB : A ⊆ B), ¬ ∃ h : P.solutions B,
      ∀ i : ↥A, h.val ⟨i.val,hAB i.property⟩ = g i := by
  classical
  by_contra hn
  apply hg
  apply (P.compact_projection A g).mpr
  intro B hAB
  by_contra h
  exact hn ⟨B,hAB,h⟩

theorem compact_projection_of_countable_source [Countable X] (A : Finset I)
    (g : ∀ i : ↥A, P.Intrinsic i.val) :
    g ∈ Set.range (P.projection A) ↔ P.FiniteExtensionProperty A g := by
  letI : Countable I := P.countable_owners
  exact P.compact_projection A g

end CCO.FiniteKernel.FinitePartition
