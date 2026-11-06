import CCO.CloneTupleGeometry.FullKernelTuple
import CCO.TransitionClosure.OriginalFiniteCylinderPartition

/-!
# B060 N05: the ACTUAL old quotient-pair spectrum detects a common clone owner

This module uses B049's genuine complete original typed quotient pair
spectrum, instantiated at the REAL pure clone source. No new abstract
spectrum is invented. In particular, it handles equality of hidden
quotient positions without treating equality as a STRONG atom.

The named diversity clone atom c belongs to a J/L class-pair spectrum
exactly if the two actual FULL quotient classes meet. Their
intersection contains an actual common clone owner, and conversely
any common owner supplies TWO DISTINCT real clones. All statements
hold for arbitrary FULL invariant J,L above K, without SAP,
terminal NR2, class Helly, or an unproved hidden quotient action.
-/

universe u v w
namespace CCO.CloneTupleGeometry

open CCO.ParityHasse.Original
open CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι)

/-- B060 N05 C28–C30: EXACT actual original typed complete
quotient-spectrum membership for the genuine new clone atom.
The quantifiers range over real clones in two true quotient
classes, and the witness is a real common point (not a fresh
artificial hidden cell or a quotient intersection axiom). -/
theorem pure_clone_quotient_spectrum_c_iff_intersection
    (J L : ColourEq (CloneSAP.source S) i)
    (hKJ : fullCloneKernel S i ≤ J)
    (hKL : fullCloneKernel S i ≤ L)
    (q : Quotient J.val) (r : Quotient L.val) :
    Sum.inr ⟨rfl⟩ ∈
        originalTypedQuotientPairSpectrum (CloneSAP.source S) J L q r ↔
      ∃ z : CloneSAP.Carrier X i,
        Quotient.mk J.val z = q ∧ Quotient.mk L.val z = r := by
  constructor
  · rintro ⟨p, s, hq, hr, hcol⟩
    have hK : fullCloneKernel S i p s :=
      (pure_clone_kernel_iff_full_colours S i p s).mpr (Or.inr hcol)
    have hLs : Quotient.mk L.val p = Quotient.mk L.val s :=
      Quotient.sound (hKL hK)
    exact ⟨p, hq, hLs.trans hr⟩
  · rintro ⟨z, hq, hr⟩
    let p : CloneSAP.Carrier X i := (z.1, z.2 + 1)
    have hzK : fullCloneKernel S i z p := rfl
    have hzJ : J z p := hKJ hzK
    have hpq : Quotient.mk J.val p = q :=
      (Quotient.sound (J.val.symm hzJ)).trans hq
    refine ⟨p, z, hpq, hr, ?_⟩
    apply (CloneSAP.source_clone_iff S p z).mpr
    refine ⟨rfl, ?_⟩
    change z.2 + 1 ≠ z.2
    exact Nat.ne_of_gt (Nat.lt_succ_self _)

/-- On actual old owners, a common quotient class witness may
always be written using the literal index-zero clone. This is
the semantically concrete owner-compatibility test: it does
not make any choice depending on a quotient class. -/
theorem pure_clone_quotient_spectrum_c_iff_owner
    (J L : ColourEq (CloneSAP.source S) i)
    (hKJ : fullCloneKernel S i ≤ J)
    (hKL : fullCloneKernel S i ≤ L)
    (q : Quotient J.val) (r : Quotient L.val) :
    Sum.inr ⟨rfl⟩ ∈
        originalTypedQuotientPairSpectrum (CloneSAP.source S) J L q r ↔
      ∃ owner : X i,
        Quotient.mk J.val ((owner, 0) : CloneSAP.Carrier X i) = q ∧
        Quotient.mk L.val ((owner, 0) : CloneSAP.Carrier X i) = r := by
  rw [pure_clone_quotient_spectrum_c_iff_intersection S i J L hKJ hKL q r]
  constructor
  · rintro ⟨z, hq, hr⟩
    refine ⟨z.1, ?_, ?_⟩
    · have hK : fullCloneKernel S i (z.1, 0) z := rfl
      exact (Quotient.sound (hKJ hK)).trans hq
    · have hK : fullCloneKernel S i (z.1, 0) z := rfl
      exact (Quotient.sound (hKL hK)).trans hr
  · rintro ⟨owner, hq, hr⟩
    exact ⟨(owner, 0), hq, hr⟩

/-- The same coordinate J with two equal hidden positions
ALWAYS realizes c through distinct clones; the hidden equality
case remains genuine equality rather than a positive identity. -/
theorem pure_clone_quotient_spectrum_c_diagonal
    (J : ColourEq (CloneSAP.source S) i)
    (hKJ : fullCloneKernel S i ≤ J)
    (q : Quotient J.val) :
    Sum.inr ⟨rfl⟩ ∈
      originalTypedQuotientPairSpectrum (CloneSAP.source S) J J q q := by
  obtain ⟨z, hz⟩ := Quotient.exists_rep q
  exact (pure_clone_quotient_spectrum_c_iff_intersection
    S i J J hKJ hKJ q q).mpr ⟨z, hz, hz⟩

/-- Every pair of actual proper MI quotient coordinates of one
original owner passes the exact semantic clone-atom
compatibility test in the accepted B049 hidden-cylinder language.
No artificial extra cell or simultaneous realization premise. -/
theorem pure_clone_original_owner_MI_spectrum_c
    (owner : X i) (J L : FullCloneProperMI S i) :
    Sum.inr ⟨rfl⟩ ∈
      originalTypedQuotientPairSpectrum
        (CloneSAP.source S) J.val L.val
        (Quotient.mk J.val.val
          ((owner, 0) : CloneSAP.Carrier X i))
        (Quotient.mk L.val.val
          ((owner, 0) : CloneSAP.Carrier X i)) := by
  apply (pure_clone_quotient_spectrum_c_iff_owner
    S i J.val L.val
    (fullCloneKernel_le_nonidentity S i J.val J.property.1)
    (fullCloneKernel_le_nonidentity S i L.val L.property.1) _ _).mpr
  exact ⟨owner, rfl, rfl⟩

end CCO.CloneTupleGeometry
