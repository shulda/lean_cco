import CCO.CloneTupleGeometry.PureKernel
import CCO.RealClosure.SAP.MIReconstruction

/-!
# B060 genuine FULL original clone-kernel MI lattice and separation

The poset is the ACTUAL finite colour-invariant equivalence lattice
of the full cloned named source. It is not an exact or synthetically
represented sublattice, and logical equality is not discarded.

No distributivity hypothesis is imposed: finite semilattice meet
decomposition is sufficient to separate the actual clone kernel.
The later terminal phase preservation, named hidden coordinates and
joint class Helly still require their own original-source proofs.
-/

universe u v w
namespace CCO.CloneTupleGeometry

open CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι)

/-- A pair of actual clones has one owner exactly when its FULL
colour is the real diagonal or the pure clone diversity atom. -/
theorem pure_clone_kernel_iff_full_colours
    (x y : CloneSAP.Carrier X i) :
    (CloneSAP.kernelSetoid (X := X) i).r x y ↔
      (CloneSAP.source S).colour x y = none ∨
        (CloneSAP.source S).colour x y = some (Sum.inr ⟨rfl⟩) := by
  constructor
  · intro h
    change x.1 = y.1 at h
    by_cases hindex : x.2 = y.2
    · left
      have heq : x = y := Prod.ext h hindex
      subst y
      exact ((CloneSAP.source S).colour_none_iff x x).mpr rfl
    · right
      exact (CloneSAP.source_clone_iff S x y).mpr ⟨h, hindex⟩
  · intro h
    rcases h with hnone | hclone
    · change x.1 = y.1
      have heq : x = y := by
        have h := ((CloneSAP.source S).colour_none_iff x y).mp hnone
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h
      exact congrArg Prod.fst heq
    · change x.1 = y.1
      exact ((CloneSAP.source_clone_iff S x y).mp hclone).1

/-- The actual clone kernel as an element of the FULL original
colour-invariant equivalence lattice, including the real diagonal.
It is *proved* colour-invariant rather than postulated. -/
def fullCloneKernel : ColourEq (CloneSAP.source S) i :=
  ⟨CloneSAP.kernelSetoid (X := X) i, by
    intro x y x' y' hcol
    have hx := pure_clone_kernel_iff_full_colours S i x y
    have hy := pure_clone_kernel_iff_full_colours S i x' y'
    rw [← hcol] at hy
    exact hx.trans hy.symm⟩

/-- Every original cloned named sort contains two distinct clones,
so the actual FULL kernel is never equality. -/
theorem fullCloneKernel_ne_bot : fullCloneKernel S i ≠ ⊥ := by
  intro h
  obtain ⟨p⟩ := S.nonemptySort i
  have hk : fullCloneKernel S i
      ((p, 0) : CloneSAP.Carrier X i) (p, 1) := rfl
  have hb : (⊥ : ColourEq (CloneSAP.source S) i)
      ((p, 0) : CloneSAP.Carrier X i) (p, 1) := by
    rw [← h]
    exact hk
  have heq : ((p, 0) : CloneSAP.Carrier X i) = (p, 1) := hb
  have hn : (0 : ℕ) = 1 := congrArg Prod.snd heq
  exact Nat.zero_ne_one hn

/-- The kernel is a genuine monolith in the FULL cloned equivalence
lattice. It is not merely minimal inside the exact-menu family. -/
theorem fullCloneKernel_le_nonidentity
    (E : ColourEq (CloneSAP.source S) i) (hE : E ≠ ⊥) :
    fullCloneKernel S i ≤ E := by
  intro x y hxy
  exact pure_clone_kernel_le_nontrivial S i E hE x y hxy

/-- Actual finite list/type of all nonidentity proper FULL MI coordinates
above K, selected by their mathematical predicate, not an abstract
quotient-action section. -/
abbrev FullCloneProperMI :=
  {J : ColourEq (CloneSAP.source S) i // J ≠ ⊥ ∧ InfIrred J}

instance fullCloneProperMI_finite : Finite (FullCloneProperMI S i) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- In the true source lattice, the proper MI elements above K are
exactly the nonidentity proper MI elements. The inclusion K ≤ J is
an actual theorem about cloned colours, not a source-side assumption. -/
theorem fullCloneKernel_mi_iff (J : ColourEq (CloneSAP.source S) i) :
    (fullCloneKernel S i ≤ J ∧ InfIrred J) ↔
      (J ≠ ⊥ ∧ InfIrred J) :=
  CCO.RealClosure.SAP.FiniteLattice.monolith_mi_family
    (fullCloneKernel_ne_bot S i)
    (fun E hE => fullCloneKernel_le_nonidentity S i E hE) J

/-- A FULL proper MI separates every strict failure of containment in K.
No distributive lattice premise and no hypothesis about terminal NR2. -/
theorem fullCloneKernel_mi_separates
    (Y : ColourEq (CloneSAP.source S) i)
    (hY : ¬ Y ≤ fullCloneKernel S i) :
    ∃ J : FullCloneProperMI S i,
      fullCloneKernel S i ≤ J.val ∧ ¬ Y ≤ J.val := by
  obtain ⟨J, hKJ, hYJ, hMI⟩ :=
    CCO.RealClosure.SAP.FiniteLattice.exists_mi_separating hY
  have hne : J ≠ ⊥ := by
    intro hbot
    rw [hbot] at hKJ
    exact (fullCloneKernel_ne_bot S i) (le_bot_iff.mp hKJ)
  exact ⟨⟨J, hne, hMI⟩, hKJ, hYJ⟩

/-- The meet of ALL proper FULL MI coordinates above the actual
clone kernel is exactly K. The empty-coordinate case correctly
means Top; no properness of K against Top is falsely inferred. -/
theorem fullCloneKernel_miMeet :
    CCO.RealClosure.SAP.FiniteLattice.miMeet (fullCloneKernel S i) =
      fullCloneKernel S i :=
  CCO.RealClosure.SAP.FiniteLattice.miMeet_eq (fullCloneKernel S i)

end CCO.CloneTupleGeometry
