import CCO.CloneTupleGeometry.FullKernelMI

/-!
# B060 realised FULL MI quotient tuples for the actual pure-clone source

For each real cloned sort, ALL nonidentity proper FULL meet-irreducible
equivalences index quotient coordinates. The kernel of the actual
quotient tuple is proved equal to the genuine clone owner kernel.
The resulting map on original owners is injective and no representative
section or pointwise choice of MI lists enters the construction.

This does NOT claim that terminal V27 unary phase splitting preserves
these exact coordinates, nor supply the later class Helly or mixed
semantic cylinder theorem. Those are separate source obligations.
-/

universe u v w
namespace CCO.CloneTupleGeometry

open CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι)

/-- The actual FULL equivalence induced by agreement in every
nonidentity proper MI quotient, with complete colour invariance. -/
def fullCloneMIKernel : ColourEq (CloneSAP.source S) i :=
  ⟨{
    r := fun x y => ∀ J : FullCloneProperMI S i, J.val x y
    iseqv := ⟨
      (fun x J => J.val.val.refl x),
      (fun {_ _} h J => J.val.val.symm (h J)),
      (fun {_ _ _} hxy hyz J => J.val.val.trans (hxy J) (hyz J))
    ⟩
  }, by
    intro x y x' y' hc
    constructor
    · intro h J
      exact (J.val.property x y x' y' hc).mp (h J)
    · intro h J
      exact (J.val.property x y x' y' hc).mpr (h J)⟩

/-- B060 N04: membership in all actual proper MI quotients
recovers exactly the real clone kernel. The proof uses genuine
finite-lattice MI separation, not lattice distributivity or an
unproved terminal quotient-SAP provider. -/
theorem fullCloneMIKernel_eq_fullCloneKernel :
    fullCloneMIKernel S i = fullCloneKernel S i := by
  apply le_antisymm
  · apply (CCO.RealClosure.SAP.FiniteLattice.le_iff_forall_mi
      (fullCloneKernel S i) (fullCloneMIKernel S i)).mpr
    intro J hKJ hMI
    intro x y hxy
    have hne : J ≠ ⊥ :=
      ((fullCloneKernel_mi_iff S i J).mp ⟨hKJ, hMI⟩).1
    exact hxy ⟨J, hne, hMI⟩
  · intro x y hxy J
    exact (fullCloneKernel_le_nonidentity S i J.val
      J.property.1) hxy

/-- The literal compatible MI quotient tuple (not an artificial
new multi-parent hidden cell). Its coordinate list is a FINITE
sortwise type, independent of the represented point. -/
def FullCloneMITuple :=
  ∀ J : FullCloneProperMI S i, Quotient J.val.val

def fullCloneMITuple (x : CloneSAP.Carrier X i) : FullCloneMITuple S i :=
  fun J => Quotient.mk J.val.val x

/-- Exact fibre formula for a real clone tuple: two tuples coincide
if and only if their underlying owners coincide. This includes the
possible empty MI-index type when a sort has only one owner. -/
theorem fullCloneMITuple_eq_iff (x y : CloneSAP.Carrier X i) :
    fullCloneMITuple S i x = fullCloneMITuple S i y ↔ x.1 = y.1 := by
  constructor
  · intro htuple
    have hmi : fullCloneMIKernel S i x y := by
      intro J
      exact Quotient.exact (congrFun htuple J)
    rw [fullCloneMIKernel_eq_fullCloneKernel S i] at hmi
    exact hmi
  · intro howner
    funext J
    apply Quotient.sound
    exact (fullCloneKernel_le_nonidentity S i J.val
      J.property.1) howner

/-- The canonical original-owner tuple, defined on all owners by
selecting the literal clone index zero, not a section of a quotient. -/
def originalOwnerMITuple (q : X i) : FullCloneMITuple S i :=
  fullCloneMITuple S i (q, 0)

/-- Clone index does not affect the canonical quotient tuple. -/
theorem originalOwnerMITuple_eq_clone (q : X i) (n : ℕ) :
    originalOwnerMITuple S i q = fullCloneMITuple S i (q, n) :=
  (fullCloneMITuple_eq_iff S i (q, 0) (q, n)).mpr rfl

/-- Injectivity of the actual finite MI-coordinate encoding on
the original owner sort, including degenerate one-owner sorts. -/
theorem originalOwnerMITuple_injective :
    Function.Injective (originalOwnerMITuple S i) := by
  intro q r h
  exact (fullCloneMITuple_eq_iff S i (q, 0) (r, 0)).mp h

end CCO.CloneTupleGeometry
