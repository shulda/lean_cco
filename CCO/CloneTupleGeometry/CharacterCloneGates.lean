import CCO.CloneTupleGeometry.DiagonalAndMeet
import CCO.PairSafeSplit.SAP.Gates
import CCO.CloneSAP.Amalgamation
import CCO.CloneSAP.Homogeneity

/-!
# B060 N02: actual character-phase global markings respect pure clone fibres

This is not a theorem about an arbitrary unary label. The phase P is the
actual reached rigid-groupoid maximal-character SourcePhase of B044/B047,
and its marking satisfies the genuine complete old-colour masks.

In the real pure-clone source, original AP proves SAP; the accepted
SAP gate theorem proves EVERY reached gate is nonidentity. Our actual
FULL cloned lattice monolith theorem then puts the clone kernel
inside each reached gate, and the accepted marking-gate theorem
forces its phase bits to agree. Inactive sorts have the fixed zero bit.

This proves one *actual-source character splitting step* preserves
entire clone fibres without assuming clone-saturated markings. The
iteration through the homogeneous marked Fraisse limit is a separate
remaining B060 obligation.
-/

universe u v w t
namespace CCO.CloneTupleGeometry

open APCharacter RigidGroupoid.Geometry
open CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- B060 N02 C06–C11 (one actual source step). ANY true global
character marking of the pure-clone old source is constant on every
whole clone fibre. The nonidentity gate premise is DISCHARGED by
actual old AP via source SAP; no invented family of marked ages,
quotient SAP, or independent arbitrary unary labels are inserted. -/
theorem pure_clone_character_marking_fibre_const
    (H : HomogeneousSource S G) (ap : AgeAP S)
    (C : ExactCalculus (CloneSAP.source S))
    {r : ι} {A : Kernel (CloneSAP.source S) r}
    (P : SourcePhase (CloneSAP.source S) (CloneSAP.homogeneous S H) C A)
    (mark : Sigma (CloneSAP.Carrier X) → Bit)
    (hm : P.masks.GlobalMarking mark)
    (i : ι) (q : X i) (m n : ℕ) :
    mark ⟨i,(q,m)⟩ = mark ⟨i,(q,n)⟩ := by
  by_cases hActive : Nonempty (Bridge (CloneSAP.source S) A i)
  · let b : Reached (CloneSAP.source S) A := ⟨i,hActive⟩
    have sapClone : AgeSAP (CloneSAP.source S) :=
      CloneSAP.strong_amalgamation S ap
    have hNonzero : PairSafeSplit.SAP.reachedKernelEq P b ≠ ⊥ :=
      PairSafeSplit.SAP.reached_kernel_ne_bot P sapClone b
    have hMono : fullCloneKernel S i ≤ PairSafeSplit.SAP.reachedKernelEq P b :=
      fullCloneKernel_le_nonidentity S i _ hNonzero
    have hGate : (Reached.kernel (CloneSAP.homogeneous S H) C b).rel
        (q,m) (q,n) := by
      change (PairSafeSplit.SAP.reachedKernelEq P b) (q,m) (q,n)
      exact hMono (show fullCloneKernel S i (q,m) (q,n) from rfl)
    exact (PairSafeSplit.SAP.marking_gate_eq
      P mark hm b (q,m) (q,n) hGate).symm
  · have hZeroM : mark ⟨i,(q,m)⟩ = 0 :=
      (hm.1 ⟨i,(q,m)⟩) hActive
    have hZeroN : mark ⟨i,(q,n)⟩ = 0 :=
      (hm.1 ⟨i,(q,n)⟩) hActive
    exact hZeroM.trans hZeroN.symm

/-- Literal owner-factorization of all genuinely character-compatible
phase bits in this old pure-clone source. The owner tag is the value
on the zero-index clone, which is independent of the chosen clone;
nothing is chosen separately per point or quotient class. -/
theorem pure_clone_character_marking_owner_factor
    (H : HomogeneousSource S G) (ap : AgeAP S)
    (C : ExactCalculus (CloneSAP.source S))
    {r : ι} {A : Kernel (CloneSAP.source S) r}
    (P : SourcePhase (CloneSAP.source S) (CloneSAP.homogeneous S H) C A)
    (mark : Sigma (CloneSAP.Carrier X) → Bit)
    (hm : P.masks.GlobalMarking mark) :
    ∃ ownerMark : Sigma X → Bit,
      ∀ (i : ι) (q : X i) (n : ℕ),
        mark ⟨i,(q,n)⟩ = ownerMark ⟨i,q⟩ := by
  refine ⟨fun p => mark ⟨p.1,(p.2,0)⟩, ?_⟩
  intro i q n
  exact pure_clone_character_marking_fibre_const S H ap C P mark hm i q n 0

end CCO.CloneTupleGeometry
