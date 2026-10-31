import CCO.ExactEPGeometry.CurrentBridgeOldSquare

/-!
# B062 C51–C54: old bridge square is beneath the canonical ORIGINAL gate

The current bridge is an ACTUAL full RAW-exact Arrow between genuine
current sorts, and the original-to-current unary reduct has its proved
two-way exact trace and displayed-middle (TP) certificates. From the
real old D extracted by the preceding source theorem, construct the
original FULL-exact composition D;Dᵒᵖ. It contains the whole original
diagonal by OLD seriality and REAL converse, not by presupposing that D
itself is reflexive (a cross-type bridge need not be).

The exact current p-trace of this original reflexive square is the
genuine current kernel K_p by the source C51 two-Peircian TP theorem.
The already proved original stable-power E2/E3 envelope therefore
shows D;Dᵒᵖ <= L_p(K_p), without adding this inequality as a premise.

No quotient SAP, old/current group section, mixed-type commutativity,
or assumption that arbitrary exact quotients are exact in reverse.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- A REAL current exact bridge kernel, viewed as an actual member
of the finite current full RAW-exact equivalence lattice. Its
colour-invariance follows from its genuinely FULL-exact relation,
not from an independent new premise. -/
def current_kernel_exact_eq
    (B : CurrentSource.{u,v,w,t}) {p : B.Sorts}
    (K : Kernel B.source p) : ExactEq B.source p := by
  have hInv : TRel.Invariant (G := B.G) K.rel :=
    K.exact.invariant B.source B.homogeneous
  exact ⟨⟨K.setoid,
    groupInvariant_colourInvariant B.source B.homogeneous hInv⟩,
    K.exact⟩

/-- Source C51: the ACTUAL full bridge R determines one genuine original
RAW-exact D, and its old equality-inclusive square D;Dᵒᵖ is BOUNDED
by the canonical largest ORIGINAL full RAW-exact gate L_p(K_p).
The current bridge, both source strengths and all original equivalence
closures are derived, not inserted as hypotheses.

In the ONE-original-sort B062 application, Dᵒᵖ=D by original
same-sort symmetric homogeneity; that identification is separate. -/
theorem current_arrow_old_square_below_largest
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    {p q : B.Sorts}
    (Kp : Kernel B.source p) (Kq : Kernel B.source q)
    (R : Arrow B.source Kp Kq) :
    ∃ D : RawExact.NonemptyExact A.source (P.parent p) (P.parent q),
      (∀ x : B.Point p, ∀ y : B.Point q,
        R.rel x y ↔ RawExact.evaluate A.source D.words
          (P.point p x) (P.point q y)) ∧
      (∀ a b : A.Point (P.parent p),
        TRel.comp (RawExact.evaluate A.source D.words)
          (TRel.converse (RawExact.evaluate A.source D.words)) a b →
        PrefixExactLargestLift.largest A B P transport tp p
          (current_kernel_exact_eq B Kp) a b) := by
  obtain ⟨D,hBridge,hGateP,_⟩ :=
    current_arrow_old_square_traces A B P transport tp Kp Kq R
  let oldR := RawExact.evaluate A.source D.words
  have hRFull : FullExact A.source oldR := ⟨D,rfl⟩
  have hSqFull : FullExact A.source
      (TRel.comp oldR (TRel.converse oldR)) :=
    (exactCalculus_of_homogeneous_CCO
      A.source A.homogeneous A.cco).comp hRFull
        (fullExact_converse A.source hRFull)
  obtain ⟨Q,hQ⟩ := hSqFull
  have hSerial : TRel.Serial oldR :=
    hRFull.serial A.source A.homogeneous
  have hRef : ∀ a : A.Point (P.parent p),
      RawExact.evaluate A.source Q.words a a := by
    intro a
    rw [hQ]
    obtain ⟨b,hab⟩ := hSerial a
    exact ⟨b,hab,hab⟩
  have hTrace (x z : B.Point p) :
      (current_kernel_exact_eq B Kp) x z ↔
        RawExact.evaluate A.source Q.words
          (P.point p x) (P.point p z) := by
    change Kp.rel x z ↔ _
    rw [hQ]
    exact hGateP x z
  have hBound :=
    original_reflexive_exact_below_largest A B P transport tp
      p (current_kernel_exact_eq B Kp) Q hRef hTrace
  refine ⟨D,hBridge,?_⟩
  intro a b hab
  apply hBound a b
  rw [hQ]
  exact hab

end
end CCO.ExactEPGeometry
