import CCO.ExactEPGeometry.OriginalOccupancyOrbitals

/-!
# B062 C97 / I10: exact image of an actual quotient atomic block

The complete E-saturation of every REAL current source pair orbital
projects to precisely ONE actual all-parent E-quotient orbital, including
the equality colour. This strengthens the existing pointwise pullback
theorem by a full image equality on arbitrary quotient points.

The proof uses actual surjectivity of each local E-class quotient and
the already proved true quotient orbital pullback; it introduces
neither quotient SAP nor an automorphism group section.

The subsequent selected odd-pivot proof must instantiate this theorem
with the genuine phase odd diversity atom, and separately prove that
its quotient orbital remains outside the projected full gate.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The image of the ENTIRE literal E-saturated old pair-colour block
is exactly the actual quotient pair colour, on every pair of true
quotient E-classes. Logical equality is treated as its real block,
not replaced by a diversity letter. -/
theorem originalExactAllCurrentPairBlock_image
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {i j : B.Sorts} (x : B.Point i) (y : B.Point j) :
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
    ∀ (p : Q.Point i) (q : Q.Point j),
      Quotient.image
        (fun z : B.Point i => (Quotient.mk'' z : Q.Point i))
        (fun z : B.Point j => (Quotient.mk'' z : Q.Point j))
        (Quotient.block B.source
          (originalExactCurrentKernelWords A B P transport base hOne E)
          (B.source.colour x y)) p q ↔
        Q.source.rawAtomRel
          (Q.source.colour (Quotient.mk'' x : Q.Point i)
            (Quotient.mk'' y : Q.Point j)) p q := by
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hOne E
  change ∀ (p : Q.Point i) (q : Q.Point j),
      Quotient.image
        (fun z : B.Point i => (Quotient.mk'' z : Q.Point i))
        (fun z : B.Point j => (Quotient.mk'' z : Q.Point j))
        (Quotient.block B.source
          (originalExactCurrentKernelWords A B P transport base hOne E)
          (B.source.colour x y)) p q ↔
        Q.source.rawAtomRel
          (Q.source.colour (Quotient.mk'' x : Q.Point i)
            (Quotient.mk'' y : Q.Point j)) p q
  intro p q
  constructor
  · rintro ⟨a,b,ha,hb,hBlock⟩
    have hPair := (originalExactAllCurrentPairBlock
      A B P transport base hOne E x a y b).mp hBlock
    simpa only [ha,hb] using hPair
  · intro hPair
    obtain ⟨a,ha⟩ := Quotient.mk''_surjective p
    obtain ⟨b,hb⟩ := Quotient.mk''_surjective q
    refine ⟨a,b,ha,hb,?_⟩
    apply (originalExactAllCurrentPairBlock
      A B P transport base hOne E x a y b).mpr
    simpa only [ha,hb] using hPair

end
end CCO.ExactEPGeometry
