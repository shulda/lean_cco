import CCO.CloneTupleGeometry.FullKernelMI
import CCO.ParityHasse.Original.RelativeIndices
import Mathlib.Data.Set.Finite.Basic

/-!
# B060 genuine finite-index intervals have nonidentity lower endpoint

An original pure clone sort has infinite FULL K-classes, witnessed by
its literal natural-number indices. Every nonidentity FULL
colour-invariant equivalence contains K by the proven clone monolith.

Consequently NO genuine finite relative-index interval E<F can have
E=identity. This proves the relevant source gate input without
postulating an infinite quotient, a finite old carrier, or SAP/CCO.
-/

universe u v w
namespace CCO.CloneTupleGeometry

open CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i : ι}

/-- B060 N02 C06: finite original relative index of a proper
FULL colour-invariant interval forces its lower endpoint to be
nonidentity. The contradiction injects all of N into the ACTUAL
relative-class type of the finite-index interval by using distinct
real clone indices from one owner. -/
theorem pure_clone_finite_interval_lower_ne_bot
    (E F : ColourEq (CloneSAP.source S) i)
    (hEF : E < F)
    (a : CloneSAP.Carrier X i)
    [Finite (RelativeClass E.val F.val a)] :
    E ≠ ⊥ := by
  intro hE
  subst E
  have hFne : F ≠ ⊥ := ne_of_gt hEF
  have hKle : fullCloneKernel S i ≤ F :=
    fullCloneKernel_le_nonidentity S i F hFne
  let f : ℕ → RelativeClass (⊥ : ColourEq (CloneSAP.source S) i).val F.val a :=
    fun n => Quotient.mk _
      (⟨(a.1,n), hKle (show fullCloneKernel S i a (a.1,n) from rfl)⟩ :
        {x : CloneSAP.Carrier X i // F a x})
  have hf : Function.Injective f := by
    intro m n h
    have hrel := Quotient.exact h
    change ((a.1,m) : CloneSAP.Carrier X i) = (a.1,n) at hrel
    exact congrArg Prod.snd hrel
  have hfinite : (Set.range f).Finite := Set.toFinite _
  exact (Set.infinite_range_of_injective hf) hfinite

/-- B060 N02 C06, actual complete lower-gate consequence. A finite-index
proper FULL interval E<F in the real clone source has the ENTIRE infinite
clone kernel below E; no quotient or source-SAP premise is added. -/
theorem pure_clone_finite_interval_kernel_le
    (E F : ColourEq (CloneSAP.source S) i)
    (hEF : E < F)
    (a : CloneSAP.Carrier X i)
    [Finite (RelativeClass E.val F.val a)] :
    fullCloneKernel S i ≤ E := by
  exact fullCloneKernel_le_nonidentity S i E
    (pure_clone_finite_interval_lower_ne_bot S E F hEF a)

end CCO.CloneTupleGeometry
