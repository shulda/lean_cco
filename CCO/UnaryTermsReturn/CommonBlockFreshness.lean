import CCO.UnaryTermsReturn.CommonBlockModel
import Mathlib.Data.Finset.Lattice.Fold
import Lean.Elab.Tactic.Omega

/-!
# B052 source10 C16: fresh old common-block labels and real clones

The old age-SAP construction for the actual infinite common-block
source needs two independent *finite* avoidance moves.

1. Every fixed original block b has infinitely many actual real
   points of each named sort i, so even a finite mixed-sort
   forbidden base can be avoided while retaining block b.
2. There are infinitely many original block labels themselves,
   so a new two-sorted block can be placed outside a finite old
   base.

These are explicit witnessed Nat bounds, with no SAP, CCO,
homogeneity, hidden SAP or other fresh-orbit hypothesis.
They are SAP construction inputs, not a declaration that
the complete original AgeSAP instance is already proved.
-/

namespace CCO.UnaryTermsReturn

/-- Every old block has a fresh real clone in every named original
sort, outside an ARBITRARY finite mixed-sort forbidden set.
No finite original carrier or quotient fresh point is assumed. -/
theorem commonBlockFreshClone
    (i : Bool) (b : ℕ) (forbidden : Finset (Sigma CommonBlockReal)) :
    ∃ x : CommonBlockReal i,
      x.1 = b ∧ (⟨i,x⟩ : Sigma CommonBlockReal) ∉ forbidden := by
  classical
  let bound : ℕ :=
    forbidden.sup (fun p : Sigma CommonBlockReal => p.2.2)
  refine ⟨(b,bound+1), rfl, ?_⟩
  intro hMem
  have hLe := Finset.le_sup
    (s := forbidden)
    (f := fun p : Sigma CommonBlockReal => p.2.2) hMem
  have hImpossible : bound+1 ≤ bound := by
    change bound+1 ≤ bound at hLe
    exact hLe
  omega

/-- One fresh original block label avoiding the block
coordinates of ALL points in a finite multi-sort base. -/
theorem commonBlockFreshLabel
    (forbidden : Finset (Sigma CommonBlockReal)) :
    ∃ b : ℕ, ∀ p ∈ forbidden, p.2.1 ≠ b := by
  classical
  let bound : ℕ :=
    forbidden.sup (fun p : Sigma CommonBlockReal => p.2.1)
  refine ⟨bound+1,?_⟩
  intro p hp hEq
  have hLe := Finset.le_sup
    (s := forbidden)
    (f := fun p : Sigma CommonBlockReal => p.2.1) hp
  have hBound : p.2.1 ≤ bound := by
    change p.2.1 ≤ bound at hLe
    exact hLe
  omega

/-- A new original real point in a genuinely NEW block, not
just a fresh clone within a previously occupied block. -/
theorem commonBlockFreshNewBlockPoint
    (i : Bool) (forbidden : Finset (Sigma CommonBlockReal)) :
    ∃ x : CommonBlockReal i,
      (∀ p ∈ forbidden, p.2.1 ≠ x.1) ∧
      (⟨i,x⟩ : Sigma CommonBlockReal) ∉ forbidden := by
  obtain ⟨b,hFresh⟩ := commonBlockFreshLabel forbidden
  refine ⟨(b,0),?_,?_⟩
  · exact hFresh
  · intro hMem
    exact hFresh ⟨i,(b,0)⟩ hMem rfl

end CCO.UnaryTermsReturn
