import CCO.RawExact.WalkColourIndependence
import Lean.Elab.Tactic.Omega

/-!
# B002 C13: recover complete edge-colour equivalence from indexed comparisons

A typed pair-colour equality at every corresponding consecutive
finite position (and equal list lengths) implies the original
recursive `SameEdgeColours` property. Logical equality remains
the optional colour `none`, not an artificial diversity atom.
This is the finite-list bridge from the CCO fan homomorphism's
individual numbered edge constraints to the existing genuine
old-word trace certificate API.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- One actual original typed colour match per pair of consecutive
indices determines the full `SameEdgeColours` certificate. -/
theorem sameEdgeColours_of_indexed
    (xs ys : List (Sigma X))
    (hlen : xs.length = ys.length)
    (hEdges : ∀ k : Nat,
      ∀ (hk : k + 1 < xs.length)
        (hk' : k + 1 < ys.length),
      taggedColour S (xs[k]'(by omega)) (xs[k + 1]'hk) =
        taggedColour S (ys[k]'(by omega)) (ys[k + 1]'hk')) :
    SameEdgeColours S xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => trivial
      | cons y ys =>
          simp only [List.length_nil, List.length_cons] at hlen
          omega
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil =>
              simp only [List.length_nil, List.length_cons] at hlen
              omega
          | cons y ys =>
              cases ys with
              | nil =>
                  trivial
              | cons y' rest =>
                  simp only [List.length_nil, List.length_cons] at hlen
                  omega
      | cons xNext xsTail =>
          cases ys with
          | nil =>
              simp only [List.length_nil, List.length_cons] at hlen
              omega
          | cons y ys =>
              cases ys with
              | nil =>
                  simp only [List.length_nil, List.length_cons] at hlen
                  omega
              | cons yNext ysTail =>
                  change taggedColour S x xNext = taggedColour S y yNext ∧
                    SameEdgeColours S (xNext :: xsTail) (yNext :: ysTail)
                  constructor
                  · have hFirst := hEdges 0 (by simp) (by simp)
                    simpa only [List.getElem_cons_zero,
                      List.getElem_cons_succ] using hFirst
                  · have hLenTail :
                        (xNext :: xsTail).length = (yNext :: ysTail).length := by
                      simpa only [List.length_cons, Nat.succ.injEq]
                        using hlen
                    apply ih (yNext :: ysTail) hLenTail
                    intro k hk hk'
                    have hkOrig :
                        (k + 1) + 1 < (x :: xNext :: xsTail).length := by
                      simp only [List.length_cons] at hk ⊢
                      omega
                    have hkOrig' :
                        (k + 1) + 1 < (y :: yNext :: ysTail).length := by
                      simp only [List.length_cons] at hk' ⊢
                      omega
                    have hAt := hEdges (k+1) hkOrig hkOrig'
                    simpa only [List.getElem_cons_succ] using hAt

end CCO.RawExact
