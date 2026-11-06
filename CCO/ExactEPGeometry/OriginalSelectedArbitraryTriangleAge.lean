import CCO.ExactEPGeometry.OriginalOccupancyQuotientSource
import CCO.RawExact.QuotientTriangleFullness
import CCO.SimultaneousQuotients.Source

/-!
# B062 C89: arbitrary locally legal finite unmarked selected quotient prefix

The actual selected E-occupancy quotient source has exactly one real
representative parent for each occupancy class. Its pairs carry precisely
the genuine original E-saturated current pair orbital colours.

This theorem is NOT restricted to a previously realized selected tuple:
given an ARBITRARY finite complete typed orbital diagram, with all actual
pair orbitals, correct logical equality/vertex separation, converse, and
realizable triangles, the original AP+HOM CCO provider constructs an
injective realization of the WHOLE diagram in that previously built
selected quotient source. The proof does not assume quotient SAP or
the next marked quotient age, and does not use a future tower prefix.

The next C89–C96 work must convert arbitrary quotient marked legality
into the same true local orbital/mask conditions and prove the full age
converse; triangle fullness alone is not that marked-age theorem.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open CCO.RawExact

noncomputable section

/-- Actual C89 unmarked finite-age step on the ONE-parent-per-occupancy
original-E quotient, not merely a previously realized finite tuple.
All pair relations must be true quotient orbitals, and local legality
is literal triangle realizability, including diagonal/separation. -/
theorem originalExactSelectedQuotient_arbitraryTriangleAge
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    let Q := originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E
    letI : ∀ c : Q.Sorts, MulAction B.G (Q.Point c) := Q.action
    ∀ {V : Type z} [Finite V]
      (D : ActualOrbitalDiagram B.G Q.Point V),
      D.TrianglesLegal →
      ∃ point : ∀ p : V, Q.Point (D.sort p),
        (∀ p q : V, D.relation p q (point p) (point q)) ∧
        Function.Injective
          (fun p : V => (⟨D.sort p, point p⟩ : Sigma Q.Point)) := by
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport base hOne E
  letI : ∀ c : Q.Sorts, MulAction B.G (Q.Point c) := Q.action
  let Occ := OriginalOccupancy A B P base hOne E
  let f := originalOccupancyRepresentativeEmbedding
    A B P base hOne E
  let J := originalExactCurrentKernelFamily
    A B P transport base hOne E
  let W := originalExactCurrentKernelWords
    A B P transport base hOne E
  have hW : ∀ p : B.Sorts,
      RawExact.evaluate B.source (W p).words = (J p).r :=
    originalExactCurrentKernelWords_relation A B P transport base hOne E
  let pi : ∀ c : Occ, B.Point (f c) → Q.Point c :=
    fun c x => Quotient.mk'' x
  have hSurj : ∀ c : Occ, Function.Surjective (pi c) := by
    intro c
    exact Quotient.mk''_surjective
  have hEquiv : ∀ (c : Occ),
      letI : MulAction B.G (Q.Point c) := Q.action c
      ∀ (g : B.G) (x : B.Point (f c)),
        pi c (g • x) = g • pi c x := by
    intro c
    letI : MulAction B.G (Q.Point c) := Q.action c
    intro g x
    rfl
  have hKer : ∀ c : Occ,
      GroupActions.kernel (pi c) =
        RawExact.evaluate B.source (W (f c)).words := by
    intro c
    exact CCO.SimultaneousQuotients.exact_kernel
      B.source J W hW (f c)
  change ∀ {V : Type z} [Finite V]
      (D : ActualOrbitalDiagram B.G Q.Point V),
      D.TrianglesLegal →
      ∃ point : ∀ p : V, Q.Point (D.sort p),
        (∀ p q : V, D.relation p q (point p) (point q)) ∧
        Function.Injective
          (fun p : V => (⟨D.sort p, point p⟩ : Sigma Q.Point))
  intro V _ D hTriangles
  exact actual_quotient_triangle_fullness_of_CCO
    B.source B.homogeneous B.cco
    Q.Point (fun c : Occ => f c) pi hSurj hEquiv
    (fun c : Occ => W (f c)) hKer D hTriangles

end
end CCO.ExactEPGeometry
