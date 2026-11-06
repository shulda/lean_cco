import CCO.ExactEPGeometry.OriginalAllCurrentFullExactPullback
import CCO.ExactEPGeometry.OriginalRetainedProjectedParityComplement

/-!
# B062 C101: genuine odd SourcePhase Arrow is dominant above K/E

At a retained source step E<=G, the previously constructed all-parent
E-quotient carries the actual full-exact projected gate K/E. For ANY
strictly larger genuine quotient full-exact equivalence Z, its literal
pullback W along the surjective original-E class projection is full RAW
exact in the ACTUAL old current source (C101/I10 provider). The proved
K/E pullback makes K<=W; the surjective map and strict Z>K/E make K<W.
Therefore the ACTUAL original SourcePhase.atSort dominant odd Arrow
is contained in W, and its real quotient pair images lie in Z.

No quotient SAP, quotient automorphism section, extra dominance premise,
or arbitrary mixed reverse exact descent is introduced. This lemma
does not itself claim that an unrelated quotient parity interval has
the same selected old atom.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Any genuine strictly larger full-exact quotient K/E-kernel contains
the image of EVERY pair in the true original distinguished odd Arrow,
with the original current parent b and full gate K_b fixed. -/
theorem originalRetainedProjectedOdd_dominatesStrictGate
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
    let K := Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b
    let Kq := originalCoherentAllparentProjectedKernel
      A B P transport tp base hBase E b.val K
        (original_retained_current_E_below_full_gate
          A B P transport tp hOne Kroot E hE b)
    letI : PartialOrder (Kernel Q.source b.val) :=
      kernelPartialOrder Q.source b.val
    ∀ (Z : Kernel Q.source b.val), Kq < Z →
      ∀ a z : B.Point b.val,
        (phase.atSort b).rel a z →
          Z.rel (Quotient.mk'' a : Q.Point b.val)
                (Quotient.mk'' z : Q.Point b.val) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hBase E
  letI : PartialOrder (Kernel Q.source b.val) :=
    kernelPartialOrder Q.source b.val
  letI : PartialOrder (Kernel B.source b.val) :=
    kernelPartialOrder B.source b.val
  let K := Reached.kernel B.homogeneous
    (exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco) b
  let hNested := original_retained_current_E_below_full_gate
    A B P transport tp hOne Kroot E hE b
  let Kq := originalCoherentAllparentProjectedKernel
    A B P transport tp base hBase E b.val K hNested
  let pi : B.Point b.val → Q.Point b.val := fun x => Quotient.mk'' x
  change ∀ (Z : Kernel Q.source b.val), Kq < Z →
    ∀ a z : B.Point b.val, (phase.atSort b).rel a z →
      Z.rel (pi a) (pi z)
  intro Z hStrict a z hOdd
  have hExact : FullExact B.source
      (GroupActions.pullback pi pi Z.rel) :=
    originalExactAllCurrentFullExact_pullback
      A B P transport base hBase E Z.rel Z.exact
  let W : Kernel B.source b.val :=
    ⟨Setoid.comap pi Z.setoid,hExact⟩
  have hGatePull := originalCoherentAllparentProjectedKernel_pullback
    A B P transport tp base hBase E b.val K hNested
  have hOldLE : K ≤ W := by
    intro x y hKxy
    have hGate : Kq.rel (pi x) (pi y) :=
      (Iff.of_eq (congrFun (congrFun hGatePull x) y)).mpr hKxy
    exact hStrict.le hGate
  have hOldStrict : K < W := by
    refine lt_iff_le_and_ne.mpr ⟨hOldLE,?_⟩
    intro heq
    have hZle : Z ≤ Kq := by
      intro p q hZpq
      obtain ⟨x,rfl⟩ := Quotient.mk''_surjective p
      obtain ⟨y,rfl⟩ := Quotient.mk''_surjective q
      have hWxy : W.rel x y := hZpq
      have hKxy : K.rel x y := by
        rw [heq]
        exact hWxy
      exact (Iff.of_eq (congrFun (congrFun hGatePull x) y)).mpr hKxy
    exact (not_le_of_gt hStrict) hZle
  exact (phase.atSort_dominant b) W hOldStrict a z hOdd

end
end CCO.ExactEPGeometry
