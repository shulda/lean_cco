import CCO.ExactEPGeometry.CertifiedHistoryLabels
import CCO.APCharacter.MaskReadout

/-!
# B062 C62: preserving a genuine phase bit forces the exact gate bound

On the ACTUAL current homogeneous AP+HOM CCO source, the canonical
full-character SourcePhase contains a real full connected groupoid and
a distinguished odd Arrow on its root. The odd arrow's character value
is ONE, and its dominance applies to EVERY genuine FULL RAW-exact
current equivalence strictly larger than the actual gate.

If a current FULL-exact E preserved the literal valid child bit and
were not contained in the genuine current gate K, the exact join E∨K
would strictly exceed K. Dominance makes the WHOLE root odd Arrow lie
in E∨K. The source's ACTUAL RAW-exact join formula factors its pair as
one real K-pair and one real E-pair. Both preserve the bit, contradicting
the actual legal marked-age character equation across that odd Arrow.

No assumption of quotient SAP, independent bit transport, any new
dominance/character provider or replacement of full RAW exact E by a
general invariant equivalence.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C62: a genuinely FULL RAW-exact current equivalence E on the
active root parent, whose every pair preserves the ACTUAL canonical
child tag, is below the complete current exact gate K.

The proof invokes the SOURCE-SELECTED full odd Arrow of the SAME
SourcePhase, its real character 1, genuine dominance and a real
witness. This is precisely the missing maximality direction at ONE
actual parent; the later history theorem supplies its label premise
from the final tower's actual old E-equivalence classes. -/
theorem current_exact_preserving_phase_label_le_gate
    (B : CurrentSource.{u,v,w,t})
    {i : B.Sorts} (K : Kernel B.source i)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) K)
    (E : ExactEq B.source i)
    (hLabels : ∀ x y : B.Point i, E x y →
      UnarySource.tag (SingleStep.identification B phase) i x =
        UnarySource.tag (SingleStep.identification B phase) i y) :
    E ≤ current_kernel_exact_eq B K := by
  classical
  by_contra hn
  let KF : ExactEq B.source i := current_kernel_exact_eq B K
  let Z : ExactEq B.source i :=
    ExactEq.sup B.homogeneous B.cco KF E
  let L : Kernel B.source i := ⟨Z.val.val,Z.property⟩
  have hJoin (x y : B.Point i) :
      Z x y ↔ ∃ z : B.Point i, K.rel x z ∧ E z y :=
    sup_relation_iff B.source B.homogeneous KF.val E.val x y
  have hKleL : K ≤ L := by
    intro x y hxy
    exact (hJoin x y).mpr ⟨y,hxy,E.val.val.refl y⟩
  have hEleL (x y : B.Point i) (hxy : E x y) : L.rel x y :=
    (hJoin x y).mpr ⟨x,K.setoid.refl x,hxy⟩
  have hNotLleK : ¬ L ≤ K := by
    intro hLK
    apply hn
    intro x y hxy
    exact hLK (hEleL x y hxy)
  have hStrict : K < L := by
    apply lt_iff_le_and_ne.mpr
    refine ⟨hKleL,?_⟩
    intro hEq
    exact hNotLleK (le_of_eq hEq.symm)
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let b : Reached B.source K := Reached.root K
  let T := phase.atSort b
  have hRoot : Reached.kernel B.homogeneous C b = K :=
    Reached.root_kernel B.homogeneous C (A := K)
  have hRootStrict : Reached.kernel B.homogeneous C b < L := by
    simpa only [hRoot] using hStrict
  have hDominant : Dominant
      (Reached.kernel B.homogeneous C b) T :=
    phase.atSort_dominant b
  obtain ⟨x,y,hOdd⟩ := T.exact.nonempty B.source
  have hZxy : L.rel x y :=
    hDominant L hRootStrict x y hOdd
  obtain ⟨z,hKxz,hEzy⟩ := (hJoin x y).mp hZxy
  let I := SingleStep.identification B phase
  have hKRoot : (Reached.kernel B.homogeneous C b).rel x z := by
    rw [hRoot]
    exact hKxz
  have hTagK : UnarySource.tag I i x = UnarySource.tag I i z :=
    canonical_phase_gate_preserves_child_tag B phase b x z hKRoot
  have hTagE : UnarySource.tag I i z = UnarySource.tag I i y :=
    hLabels z y hEzy
  have hTag : UnarySource.tag I i x = UnarySource.tag I i y :=
    hTagK.trans hTagE
  have hMarkEq :
      UnarySource.mark I ⟨i,x⟩ = UnarySource.mark I ⟨i,y⟩ :=
    congrArg Subtype.val hTag
  letI := Reached.groupoid B.homogeneous C (A := K)
  have hLegal :
      phase.allows (B.source.colour x y)
        (UnarySource.mark I ⟨i,x⟩) (UnarySource.mark I ⟨i,y⟩) :=
    (UnarySource.global_marking I).2 ⟨i,x⟩ ⟨i,y⟩
  have hMasked := (phase.rigid_mask_iff b b T x y hOdd
    (UnarySource.mark I ⟨i,x⟩)
    (UnarySource.mark I ⟨i,y⟩)).mp hLegal
  have hOddOne : phase.character.value T = (1 : Bit) :=
    phase.atSort_detects b
  have hFlip :
      UnarySource.mark I ⟨i,y⟩ =
        UnarySource.mark I ⟨i,x⟩ + (1 : Bit) := by
    simpa only [hOddOne] using hMasked.2.2
  have hOneZero : (1 : Bit) = 0 := by
    have he :
        UnarySource.mark I ⟨i,x⟩ + (1 : Bit) =
          UnarySource.mark I ⟨i,x⟩ + (0 : Bit) := by
      simpa only [add_zero] using hFlip.symm.trans hMarkEq.symm
    exact add_left_cancel he
  exact (by decide : (1 : Bit) ≠ 0) hOneZero

end
end CCO.ExactEPGeometry
