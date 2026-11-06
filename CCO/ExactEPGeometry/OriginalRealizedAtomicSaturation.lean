import CCO.ExactEPGeometry.ExactTraceProduct
import CCO.ExactEPGeometry.ExactEquivalenceLattice
import CCO.APCharacter.Towers.CurrentSource
import CCO.RawExact.ActualOrbitalExact
import CCO.RawExact.ExactCalculusSource

/-!
# B062 E7: original saturation of every REALIZED current atomic trace

Two applications of the genuine nonempty-input (TP) theorem identify the
complete current E-left;atom;E-right block with the literal trace of the
corresponding original saturated atom. All nonempty trace guards are
proved from the displayed actual current pair and reflexive endpoints.

The colour is the actual complete optional colour of that pair, so logical
identity is included and no arbitrary old atom is presumed to occur on
the current parent pair. The two original exact endpoint equivalences
may be on different original named sorts. Specializing them to the two
restrictions of the single original E gives the pinned source equation E7.
-/

universe u v w t
namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Source E7 on every genuinely realized complete current atom. The
OLD witnesses in the RHS are lifted into the prescribed current parents
using actual (TP), rather than a section or a quotient SAP assumption. -/
theorem originalRealizedAtomicSaturation_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (tp : ExactTraceProduct A.source B.source P)
    {i j : B.Sorts}
    (E : ExactEq A.source (P.parent i))
    (F : ExactEq A.source (P.parent j))
    (a x : B.Point i) (b y : B.Point j) :
    (∃ u : B.Point i, ∃ v : B.Point j,
      E (P.point i x) (P.point i u) ∧
      B.source.colour u v = B.source.colour a b ∧
      F (P.point j v) (P.point j y)) ↔
    ∃ u : A.Point (P.parent i), ∃ v : A.Point (P.parent j),
      E (P.point i x) u ∧
      A.source.colour u v = A.source.colour (P.point i a) (P.point j b) ∧
      F v (P.point j y) := by
  obtain ⟨D,hD⟩ := E.property
  obtain ⟨K,hK⟩ := F.property
  obtain ⟨C,hC⟩ := RawExact.actual_pair_colour_exact A.source
    (P.point i a) (P.point j b)
  let DC := RawExact.convolutionExact A.source A.homogeneous D C
  have hDC : RawExact.evaluate A.source DC.words =
      TRel.comp (RawExact.evaluate A.source D.words)
        (RawExact.evaluate A.source C.words) :=
    RawExact.convolutionExact_represents A.source A.homogeneous
      (RawExact.heterogeneousExactBallHelly_of_CCO
        A.source A.homogeneous A.cco) D C
  have hDReal : ∃ z z' : B.Point i,
      RawExact.evaluate A.source D.words (P.point i z) (P.point i z') := by
    exact ⟨a,a,by simpa only [hD] using E.val.val.refl (P.point i a)⟩
  have hCReal : ∃ z : B.Point i, ∃ z' : B.Point j,
      RawExact.evaluate A.source C.words (P.point i z) (P.point j z') := by
    exact ⟨a,b,by rw [hC]; rfl⟩
  have hKReal : ∃ z z' : B.Point j,
      RawExact.evaluate A.source K.words (P.point j z) (P.point j z') := by
    exact ⟨b,b,by simpa only [hK] using F.val.val.refl (P.point j b)⟩
  have hDCReal : ∃ z : B.Point i, ∃ z' : B.Point j,
      RawExact.evaluate A.source DC.words (P.point i z) (P.point j z') := by
    refine ⟨a,b,?_⟩
    rw [hDC]
    exact ⟨P.point i a,
      by simpa only [hD] using E.val.val.refl (P.point i a),by rw [hC]; rfl⟩
  constructor
  · rintro ⟨u,v,hxu,huv,hvy⟩
    refine ⟨P.point i u,P.point j v,hxu,?_,hvy⟩
    rw [P.colour i j u v,P.colour i j a b,huv]
  · rintro ⟨u,v,hxu,huv,hvy⟩
    have hComp : TRel.comp (RawExact.evaluate A.source DC.words)
        (RawExact.evaluate A.source K.words) (P.point i x) (P.point j y) := by
      refine ⟨v,?_,?_⟩
      · rw [hDC]
        exact ⟨u,by simpa only [hD] using hxu,by simpa only [hC,AtomicSource.rawAtomRel] using huv⟩
      · simpa only [hK] using hvy
    obtain ⟨v',hxv,hv'y⟩ := (tp.product DC K hDCReal hKReal x y).mpr hComp
    have hInner : TRel.comp (RawExact.evaluate A.source D.words)
        (RawExact.evaluate A.source C.words) (P.point i x) (P.point j v') := by
      rwa [hDC] at hxv
    obtain ⟨u',hxu',hu'v'⟩ := (tp.product D C hDReal hCReal x v').mpr hInner
    refine ⟨u',v',?_,?_,?_⟩
    · simpa only [hD] using hxu'
    · apply Option.map_injective (P.atom_injective i j)
      rw [← P.colour i j u' v',← P.colour i j a b]
      simpa only [hC,AtomicSource.rawAtomRel] using hu'v'
    · simpa only [hK] using hv'y

end
end CCO.ExactEPGeometry
