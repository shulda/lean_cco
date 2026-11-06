import CCO.AutomaticEPCore.QuotientSeparator
import CCO.ExactEPGeometry.OriginalOneSortExactDescent

/-! Source-facing B063 C25: the quotient is the actual ORIGINAL canonical
FULL EXACT quotient, and projection equivariance/invariance/kernel clauses
are constructed from its proved source instance. Only the conditional D06
quotient separator pair is input. The old endpoint labels remain prescribed. -/

universe u v w r
namespace CCO.AutomaticEPCore
open CCO.APCharacter.Towers CCO.ExactEPGeometry CCO.ParityHasse.Original
noncomputable section

abbrev originalCoreQuotient (A : CurrentSource.{u,v,w,r})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :=
  CCO.ExactCRT.CanonicalTyped.source A.source A.homogeneous
    (originalExactSourceKernelFamily A base hOne E)
    (originalExactSourceKernelWords A base hOne E)
    (originalExactSourceKernelWords_relation A base hOne E)

/-- `lem:ep-lift-separator` with the actual old canonical quotient atom.
The edge witnesses one quotient pair of real E-classes; actual I01
occupancy then realizes the exact requested old type names s,t in those
same classes. No quotient SAP, full-age provider or rank hypothesis is
assumed by the lift. -/
theorem original_quotient_bipartite_separator_lift
    (A B : CurrentSource.{u,v,w,r}) (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (b : (originalCoreQuotient A base hOne E).Atom base base)
    (bipartite : (atomGraph (originalCoreQuotient A base hOne E) b).IsBipartite)
    (p q s t : B.Sorts) (x : B.Point p) (y : B.Point q)
    (hs : prefixSupport P (originalExactGlobalRelation A base hOne E) p s)
    (ht : prefixSupport P (originalExactGlobalRelation A base hOne E) q t)
    (edge : (atomGraph (originalCoreQuotient A base hOne E) b).Adj
      (Quotient.mk'' (originalPointEquiv A base hOne (P.project ⟨p,x⟩)))
      (Quotient.mk'' (originalPointEquiv A base hOne (P.project ⟨q,y⟩)))) :
    ∃ a : A.source.Atom base base,
      (atomGraph A.source a).IsBipartite ∧ originalAtomTable A B P base hOne a s t := by
  let J := originalExactSourceKernelFamily A base hOne E
  let W := originalExactSourceKernelWords A base hOne E
  let hW := originalExactSourceKernelWords_relation A base hOne E
  let Q := fun i => Quotient (J i)
  letI := A.source.finiteSort
  letI : ∀ i, MulAction A.G (Q i) :=
    CCO.ExactCRT.CanonicalTyped.action A.source A.homogeneous J W hW
  let pi := CCO.ExactCRT.CanonicalTyped.projection J
  let T := originalCoreQuotient A base hOne E
  have equivariant :=
    CCO.ExactCRT.CanonicalTyped.projection_equivariant A.source A.homogeneous J W hW
  have hJ : J base = E.val.val := by
    rfl
  have class_fixed : ∀ u v : A.Point base, E u v → pi base u = pi base v := by
    intro u v huv
    apply Quotient.sound
    change (J base) u v
    rw [hJ]
    exact huv
  have invariant : ∀ (g : A.G) (u v : Q base),
      (atomGraph T b).Adj u v → (atomGraph T b).Adj (g • u) (g • v) := by
    intro g u v huv
    have hColour : T.colour u v = T.colour (g • u) (g • v) :=
      (CCO.ExactCRT.TypedPalette.source_colour_eq_iff_orbital
        Q A.source A.homogeneous id pi
        (CCO.ExactCRT.CanonicalTyped.projection_surjective J) equivariant
        u v (g • u) (g • v)).mpr ⟨g,rfl,rfl⟩
    change T.colour (g • u) (g • v) = some b
    exact hColour.symm.trans huv
  exact original_bipartite_separator_from_occupancy A B P base hOne E
    (pi base) (equivariant base) class_fixed
    (atomGraph T b) invariant bipartite p q s t x y hs ht edge

end
end CCO.AutomaticEPCore
