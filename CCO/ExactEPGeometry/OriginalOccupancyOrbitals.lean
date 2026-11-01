import CCO.ExactEPGeometry.OriginalOccupancyQuotientSource
import CCO.RigidGroupoid.Geometry.Quotient.Blocks

/-!
# B062 C68–C69: real occupancy quotient orbitals and local E-blocks

The C67 selected occupancy source is the actual restriction of the
ALREADY CONSTRUCTED fully typed simultaneous exact quotient source.
For each pair of selected parents, its literal current quotient
atomic block is exactly the REAL E|p²;a;E|q² block of an actually
occurring current pair atom a (including true diagonal).

This follows from the accepted, equality-inclusive
RigidGroupoid.Geometry.Quotient.block_pullback theorem and the actual
typed simultaneous quotient source. It preserves the real selected
sort names and points; no invented orbital palette, global quotient
group section, SAP or mixed RAW reverse exact descent is introduced.

Every pair in the actual occupancy-selected quotient has genuine
representatives in its selected original parent sorts. We therefore
get ALL actual quotient pair orbitals, not one chosen generating
orbit or an assertion that an arbitrary old atom occurs on each
selected parent pair.

The further N09 step identifying these current local E-blocks with
the restrictions of ORIGINAL E;a;E is separately required, using
genuine original (TP)/N03 and one-sort saturation.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.SimultaneousQuotients

noncomputable section

/-- C68 on all actual named current parents before selecting one per
occupancy: their literal simultaneous quotient pair orbit is exactly
the E-saturated genuinely occurring current atom, with the correct
old diagonal and typed quotient identity. -/
theorem originalExactAllCurrentPairBlock
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {i j : B.Sorts}
    (x a : B.Point i) (y b : B.Point j) :
    let T := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
    Quotient.block B.source
      (originalExactCurrentKernelWords A B P transport base hOne E)
      (B.source.colour x y) a b ↔
    T.source.rawAtomRel
      (T.source.colour (Quotient.mk'' x : T.Point i)
        (Quotient.mk'' y : T.Point j))
      (Quotient.mk'' a : T.Point i)
      (Quotient.mk'' b : T.Point j) := by
  dsimp only
  let J := originalExactCurrentKernelFamily A B P transport base hOne E
  let W := originalExactCurrentKernelWords A B P transport base hOne E
  have hRep : ∀ k : B.Sorts,
      RawExact.evaluate B.source (W k).words = (J k).r :=
    originalExactCurrentKernelWords_relation A B P transport base hOne E
  letI : ∀ k : B.Sorts, MulAction B.G (Quotient (J k)) :=
    CCO.SimultaneousQuotients.action B.source B.homogeneous J W hRep
  have hKer : ∀ k : B.Sorts,
      GroupActions.kernel (CCO.SimultaneousQuotients.projection J k) =
        RawExact.evaluate B.source (W k).words :=
    CCO.SimultaneousQuotients.exact_kernel B.source J W hRep
  have hColours :
      ∀ {k l : B.Sorts}
        (u : Quotient (J k)) (v : Quotient (J l))
        (u' : Quotient (J k)) (v' : Quotient (J l)),
        (CCO.SimultaneousQuotients.source
          B.source B.homogeneous J W hRep).colour u v =
        (CCO.SimultaneousQuotients.source
          B.source B.homogeneous J W hRep).colour u' v' ↔
          GroupActions.orbital (G := B.G) u v u' v' :=
    CCO.SimultaneousQuotients.actual_colours
      B.source B.homogeneous J W hRep
  have hBlock :=
    Quotient.block_pullback B.source
      (CCO.SimultaneousQuotients.source
        B.source B.homogeneous J W hRep)
      B.homogeneous
      (CCO.SimultaneousQuotients.projection J)
      (CCO.SimultaneousQuotients.equivariant
        B.source B.homogeneous J W hRep)
      W hKer hColours x y
  have hApplied := congrFun (congrFun hBlock a) b
  exact hApplied

/-- C68 on the ACTUAL one-parent-per-occupancy subsource. Its colours
are literally those of the accepted all-parent quotient source at
the selected representative names; the only change is the SORT
index, never an orbital quotient or fresh point. -/
theorem originalExactSelectedPairBlock
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (c d : OriginalOccupancy A B P base hOne E)
    (x a : B.Point (originalOccupancyRepresentative A B P base hOne E c))
    (y b : B.Point (originalOccupancyRepresentative A B P base hOne E d)) :
    let Q := originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E
    Quotient.block B.source
      (originalExactCurrentKernelWords A B P transport base hOne E)
      (B.source.colour x y) a b ↔
    Q.source.rawAtomRel
      (Q.source.colour (Quotient.mk'' x : Q.Point c)
        (Quotient.mk'' y : Q.Point d))
      (Quotient.mk'' a : Q.Point c)
      (Quotient.mk'' b : Q.Point d) := by
  dsimp only
  exact originalExactAllCurrentPairBlock
    A B P transport base hOne E x a y b

/-- Source C69: EVERY actual quotient pair orbital on the selected
occupancy names comes from SOME ACTUALLY REALIZED old-current pair
colour on the selected parents, with complete E-saturation. This is
not a statement about nominal atoms that never occur on a type pair.
-/
theorem everyOriginalExactSelectedPairBlock
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (c d : OriginalOccupancy A B P base hOne E)
    (q : (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point c)
    (r : (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point d) :
    ∃ x : B.Point (originalOccupancyRepresentative A B P base hOne E c),
      ∃ y : B.Point (originalOccupancyRepresentative A B P base hOne E d),
        (Quotient.mk'' x :
          (originalExactSelectedQuotientCurrentSource
            A B P transport base hOne E).Point c) = q ∧
        (Quotient.mk'' y :
          (originalExactSelectedQuotientCurrentSource
            A B P transport base hOne E).Point d) = r ∧
        ∀ (a : B.Point
            (originalOccupancyRepresentative A B P base hOne E c))
          (b : B.Point
            (originalOccupancyRepresentative A B P base hOne E d)),
          Quotient.block B.source
            (originalExactCurrentKernelWords A B P transport base hOne E)
            (B.source.colour x y) a b ↔
          (originalExactSelectedQuotientCurrentSource
            A B P transport base hOne E).source.rawAtomRel
              ((originalExactSelectedQuotientCurrentSource
                A B P transport base hOne E).source.colour q r)
              (Quotient.mk'' a) (Quotient.mk'' b) := by
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      refine ⟨x,y,rfl,rfl,?_⟩
      intro a b
      exact originalExactSelectedPairBlock
        A B P transport base hOne E c d x a y b

end
end CCO.ExactEPGeometry
