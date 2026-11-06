import CCO.TypedOrbitFrames.ActualMeetEquivalence
import CCO.RealClosure.Bounds.TerminalLattice

/-!
# B053 C26--C33: true source-specific finite class-incidence Helly

In the standing original terminal symmetric-on-sorts setting,
every FULL original colour-invariant equivalence is an ACTUAL
RAW exact equivalence by accepted B011 under original FULL NR2.
Original semantic homomorphic CCO and accepted B008 supply
the exact-class finite Helly theorem for those very old
equivalences. Thus a pairwise-intersecting finite family of
ACTUAL old class vertices has ONE common original real point.

This is genuine source-specific old Helly, not a conditional
abstract-Helly provider and not a hidden SAP assumption.
Both the empty list and finite repeated coordinates are included.

The second theorem combines that actual old common witness
with B053's verified infinite full-cover relative-index
result to give infinite unforced J classes in the SAME fibre.
This does not yet give simultaneous avoidance of multiple
J-coordinate forbidden lists; the single-action Neumann
argument is a separate remaining source obligation.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original
open CCO.ExactCRT
open CCO.RealClosure.Bounds

universe u v w t
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Every pairwise-compatible family of ACTUAL FULL original
equivalence classes has ONE actual old real point in their
joint intersection. Uses exact original RAW Helly, not
an abstract free Helly assumption or hidden-age SAP. -/
theorem original_terminal_actual_pairwise_class_helly
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (nr2 : SortNR2 S i)
    {m : Nat}
    (E : Fin m → ColourEq S i) (c : Fin m → X i)
    (hPair : ∀ j k : Fin m,
      ∃ x : X i, E j (c j) x ∧ E k (c k) x) :
    ∃ x : X i, x ∈ originalActualClassFibre S E c := by
  let e : Fin m → ExactEq S H cco i :=
    fun j => ⟨(E j).val, terminal_all_exact S H nr2 (E j)⟩
  have hPair' : ∀ j k : Fin m,
      ∃ x : X i, (e j).val (c j) x ∧ (e k).val (c k) x :=
    hPair
  obtain ⟨x, hx⟩ :=
    Abstract.classHelly_finite
      (exactSublattice S H cco i)
      (exact_classHelly S H cco i) e c hPair'
  exact ⟨x, fun j => hx j⟩

/-- The actual original FULL exact-ball Helly witness is
combined with the literal infinite FULL-cover assumption:
an unforced J coordinate assumes infinitely many ACTUAL
J-quotient values in the common original real fibre.
No named-quotient/hidden SAP or independent choices are used. -/
theorem original_terminal_common_fibre_unforced_classes_infinite
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (nr2 : SortNR2 S i)
    {m : Nat}
    (E : Fin m → ColourEq S i) (c : Fin m → X i)
    (hPair : ∀ j k : Fin m,
      ∃ x : X i, E j (c j) x ∧ E k (c k) x)
    (hCover : OriginalAllFullCoversInfinite S (i := i))
    (J : ColourEq S i)
    (hnot : ¬ originalActualMeetEquivalence S E ≤ J) :
    ∃ x : X i, x ∈ originalActualClassFibre S E c ∧
      Infinite {q : Quotient J.val //
         ∃ y : X i, y ∈ originalActualClassFibre S E c ∧
            Quotient.mk J.val y = q} := by
  obtain ⟨x, hx⟩ :=
    original_terminal_actual_pairwise_class_helly
      S H cco nr2 E c hPair
  exact ⟨x,hx,
    original_unforced_J_classes_in_actual_common_fibre
      S hCover E c x hx J hnot⟩

end CCO.TypedOrbitFrames
