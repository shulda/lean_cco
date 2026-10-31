import CCO.ExactEPGeometry.PrefixExactRestrictionJoin
import CCO.ExactEPGeometry.ExactEquivalenceComplete
import CCO.ExactEPGeometry.LargestLift

/-!
# B062 E2/E3: the canonical largest ORIGINAL exact lift of a current gate

A genuine surjective finite-lattice homomorphism `rho_p` has a RIGHT
ADJOINT, obtained by taking the join of all original exact equivalences
whose trace is below the desired current equivalence. Since the actual
source restriction is surjective, that largest right-adjoint value maps
to the desired current exact equivalence exactly, and is the greatest
member of its original exact fiber.

Here ALL inputs are the real RAW-exact finite lattices and the actual
canonical-source exact/TP certificates. No full-invariant nonexact
equivalence, quotient SAP, arbitrary section or new axiom is inserted.
-/

universe u v w t

namespace CCO.ExactEPGeometry.PrefixExactLargestLift

open APCharacter.Towers
open CCO.ExactEPGeometry
open CCO.ExactEPGeometry.PrefixExactRestriction
open CCO.RigidGroupoid.Geometry

noncomputable section

/-- Source E2/E3 with the ACTUAL represented finite exact-equivalence
lattices: the canonical largest original exact fiber element exists,
maps to F, and its universal property is precisely the right adjunction.
The finite exact lattice is completed using Mathlib's finite construction;
the real restriction's join preservation is the proved C28 (TP) instance. -/
theorem exists_largest
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts) (F : ExactEq B.source p) :
    ∃ L : ExactEq A.source (P.parent p),
      rho A B P transport p L = F ∧
      ∀ E : ExactEq A.source (P.parent p),
        rho A B P transport p E ≤ F ↔ E ≤ L := by
  letI : CompleteLattice (ExactEq A.source (P.parent p)) :=
    ExactEq.completeLattice A.source A.homogeneous A.cco (P.parent p)
  letI : CompleteLattice (ExactEq B.source p) :=
    ExactEq.completeLattice B.source B.homogeneous B.cco p
  let restriction : ExactEq A.source (P.parent p) →o ExactEq B.source p :=
    rhoOrder A B P transport p
  have hBot : restriction ⊥ = ⊥ := rho_bot A B P transport p
  have hJoin :
      ∀ E K : ExactEq A.source (P.parent p),
        restriction (E ⊔ K) = restriction E ⊔ restriction K := by
    intro E K
    change rho A B P transport p
        (ExactEq.sup A.homogeneous A.cco E K) =
      ExactEq.sup B.homogeneous B.cco
        (rho A B P transport p E) (rho A B P transport p K)
    exact rho_sup A B P transport tp p E K
  have hSurj : Function.Surjective restriction :=
    rho_surjective A B P transport tp p
  obtain ⟨hMaps,hAdj⟩ :=
    LargestLift.finite_exact_fiber_adjoint
      restriction hBot hJoin hSurj F
  exact ⟨LargestLift.largestLift restriction F,hMaps,hAdj⟩

/-- The canonical original lift is chosen from the PROVED finite
exact-fiber maximum. This is a genuine object of the original FULL
RAW-exact equivalence lattice, not an arbitrary predecessor. -/
def largest
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts) (F : ExactEq B.source p) :
    ExactEq A.source (P.parent p) :=
  Classical.choose (exists_largest A B P transport tp p F)

/-- Source E2 and E3 simultaneously: canonical largest lift maps
EXACTLY to F and satisfies the full order adjunction, not merely
the largest-fiber inequality in one direction. -/
theorem largest_spec
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts) (F : ExactEq B.source p) :
    rho A B P transport p (largest A B P transport tp p F) = F ∧
      ∀ E : ExactEq A.source (P.parent p),
        rho A B P transport p E ≤ F ↔
          E ≤ largest A B P transport tp p F :=
  Classical.choose_spec (exists_largest A B P transport tp p F)

/-- Largest-fiber (E2) maximality is a consequence, not an assumed
provider. Any old exact equivalence with the same actual trace lies
below the canonical original lift. -/
theorem largest_dominates
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts) (F : ExactEq B.source p)
    (E : ExactEq A.source (P.parent p))
    (h : rho A B P transport p E = F) :
    E ≤ largest A B P transport tp p F :=
  ((largest_spec A B P transport tp p F).2 E).mp (le_of_eq h)

/-- Actual C28 canonical safe-history E2/E3 source instance with NO
external lift or lattice-homomorphism hypothesis. -/
theorem canonical_prefix_largest
    {A B : CurrentSource.{u,v,w,t}}
    (h : History CanonicalHistoryExact.CanonicalStep A B)
    (p : B.Sorts) (F : ExactEq B.source p) :
    let P := CanonicalHistoryExact.historyReduct
      (CanonicalHistoryExact.exactHistory h)
    ∃ L : ExactEq A.source (P.parent p),
      rho A B P (CanonicalHistoryExact.canonical_history_transport h) p L = F ∧
      ∀ E : ExactEq A.source (P.parent p),
        rho A B P (CanonicalHistoryExact.canonical_history_transport h) p E ≤ F ↔
          E ≤ L := by
  dsimp only
  exact exists_largest A B _
    (CanonicalHistoryExact.canonical_history_transport h)
    (CanonicalHistoryExact.canonical_history_product h) p F


/-- Literal source E2 formula: L_p(F) is exactly the join of ALL original
RAW-exact equivalences with precisely the designated current trace.
This is an exact finite fiber, not the lattice of arbitrary invariant
equivalences. Since L_p(F) itself belongs to that fiber and dominates
all its members, no unproved choice or abstract fiber completeness
hypothesis remains. -/
theorem largest_eq_fiber_sup
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts) (F : ExactEq B.source p) :
    letI := ExactEq.completeLattice A.source A.homogeneous A.cco
      (P.parent p)
    largest A B P transport tp p F =
      sSup {E : ExactEq A.source (P.parent p) |
        rho A B P transport p E = F} := by
  apply le_antisymm
  · apply le_sSup
    exact (largest_spec A B P transport tp p F).1
  · apply sSup_le
    intro E hE
    exact largest_dominates A B P transport tp p F E hE

/-- The right adjoint preserves the empty meet: the maximal original
exact lift of current Top is ORIGINAL Top, not Id. -/
theorem largest_top
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts) :
    largest A B P transport tp p (⊤ : ExactEq B.source p) =
      (⊤ : ExactEq A.source (P.parent p)) := by
  apply top_unique
  exact ((largest_spec A B P transport tp p ⊤).2 ⊤).mp le_top

/-- E3 also gives preservation of the BINARY meet. Along with the
proved Top case, this establishes ALL finite meets, including the
empty one, at actual source strength. -/
theorem largest_inf
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts) (F K : ExactEq B.source p) :
    largest A B P transport tp p (F ⊓ K) =
      largest A B P transport tp p F ⊓
      largest A B P transport tp p K := by
  apply le_antisymm
  · apply le_inf
    · apply ((largest_spec A B P transport tp p F).2 _).mp
      exact (le_of_eq (largest_spec A B P transport tp p (F ⊓ K)).1).trans
        inf_le_left
    · apply ((largest_spec A B P transport tp p K).2 _).mp
      exact (le_of_eq (largest_spec A B P transport tp p (F ⊓ K)).1).trans
        inf_le_right
  · apply ((largest_spec A B P transport tp p (F ⊓ K)).2 _).mp
    apply le_inf
    · have h := (rho_mono A B P transport p)
          (inf_le_left :
            largest A B P transport tp p F ⊓
              largest A B P transport tp p K ≤
                largest A B P transport tp p F)
      rw [(largest_spec A B P transport tp p F).1] at h
      exact h
    · have h := (rho_mono A B P transport p)
          (inf_le_right :
            largest A B P transport tp p F ⊓
              largest A B P transport tp p K ≤
                largest A B P transport tp p K)
      rw [(largest_spec A B P transport tp p K).1] at h
      exact h

end
end CCO.ExactEPGeometry.PrefixExactLargestLift
