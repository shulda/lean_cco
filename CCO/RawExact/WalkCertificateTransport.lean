import CCO.RawExact.WalkColourIndependence

/-!
# B002 C13: certified RAW word walks survive old-colour-preserving maps

A genuine original RAW word witness has a colour-certified list
of original points. Any OTHER list with the SAME original sort trace
and the SAME full typed colour on every corresponding consecutive
edge is also a certified walk of the SAME genuine original atoms.

This does not postulate injectivity of the new points, and genuine
identity letters contribute no edges. Its consumer will recover a
new real WordPath along the source-CCO completed private fan.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The FULL original atom-sequence certificate transfers to a
new set of real points if their original sort trace and each
old typed pair colour are exactly preserved. -/
theorem typedWalkCertificate_of_same_colours
    {points points' : List (Sigma X)}
    {steps : List (TypedAtomicStep S)}
    (h : TypedWalkCertificate S points steps)
    (hSame : SameEdgeColours S points points')
    (hSort : points.map Sigma.fst = points'.map Sigma.fst) :
    TypedWalkCertificate S points' steps := by
  induction h generalizing points' with
  | singleton p =>
      cases points' with
      | nil =>
          cases hSort
      | cons q rest =>
          cases rest with
          | nil =>
              exact TypedWalkCertificate.singleton q
          | cons r tail =>
              cases hSame
  | step x y a edge rest ih =>
      cases points' with
      | nil =>
          cases hSame
      | cons p' tail' =>
          cases tail' with
          | nil =>
              cases hSame
          | cons q' rest' =>
              rcases p' with ⟨i', x'⟩
              rcases q' with ⟨j', y'⟩
              have hi : (⟨_, x⟩ : Sigma X).1 = i' :=
                (List.cons.inj hSort).1
              have hj : (⟨_, y⟩ : Sigma X).1 = j' :=
                (List.cons.inj (List.cons.inj hSort).2).1
              subst i'
              subst j'
              have hEdgeColour :
                  S.colour x y = S.colour x' y' := by
                simpa only [SameEdgeColours, taggedColour,
                  Sigma.mk.injEq, heq_eq_eq, true_and] using hSame.1
              have hEdge' : S.atomRel a x' y' := by
                change S.colour x' y' = some a
                exact hEdgeColour.symm.trans edge
              have hTailSort := (List.cons.inj hSort).2
              exact TypedWalkCertificate.step x' y' a hEdge'
                (ih hSame.2 hTailSort)

end CCO.RawExact
