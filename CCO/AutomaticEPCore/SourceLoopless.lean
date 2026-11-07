import CCO.AutomaticEPCore.OriginalTypes
import CCO.AutomaticEPCore.TerminalLoopless

/-! The actual source application of B063 C08. The literal unary reduct
and the original colour equation establish invariance of an old atom's
restriction. No Phi composition/meet theorem, quotient tower or assumed
loopless table is used to discharge this application. -/

universe u v w t
namespace CCO.AutomaticEPCore

open CCO.APCharacter.Towers CCO.ParityHasse.Original CCO.ExactEPGeometry
noncomputable section

/-- Equal current pair colours have equal actual old one-sort colours,
with the required original sort equality retained explicitly. -/
theorem original_restricted_colour_eq
    (A B : CurrentSource.{u,v,w,t}) (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (p : B.Sorts) (x y x' y' : B.Point p)
    (hcol : B.source.colour x y = B.source.colour x' y') :
    A.source.colour
        (originalPointEquiv A base hOne (P.project ⟨p,x⟩))
        (originalPointEquiv A base hOne (P.project ⟨p,y⟩)) =
      A.source.colour
        (originalPointEquiv A base hOne (P.project ⟨p,x'⟩))
        (originalPointEquiv A base hOne (P.project ⟨p,y'⟩)) := by
  cases hOne (P.parent p)
  change A.source.colour (P.point p x) (P.point p y) =
    A.source.colour (P.point p x') (P.point p y')
  rw [P.colour,P.colour,hcol]

/-- `lem:ep-bp-loopless` on the actual original old-atom table of any
actual terminal prefix. Every REALIZED final sort is included. -/
theorem original_bipartite_table_loopless
    (A B : CurrentSource.{u,v,w,t}) (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (terminal : ∀ p : B.Sorts, FullCoverTerminal B.source p)
    (a : A.source.Atom base base) (bipartite : (atomGraph A.source a).IsBipartite) :
    ∀ p : B.Sorts, ¬originalAtomTable A B P base hOne a p p := by
  intro p hLoop
  obtain ⟨x,y,hxy⟩ := hLoop
  let realPoint : B.Point p → A.Point base :=
    fun x => originalPointEquiv A base hOne (P.project ⟨p,x⟩)
  have invariant : ColourInvariant B.source p
      (fun x y => (atomGraph A.source a).Adj (realPoint x) (realPoint y)) := by
    intro x y x' y' hcol
    change A.source.colour (realPoint x) (realPoint y) = some a ↔
      A.source.colour (realPoint x') (realPoint y') = some a
    rw [original_restricted_colour_eq A B P base hOne p x y x' y' hcol]
  exact terminal_bipartite_restriction_empty B.source B.homogeneous (terminal p)
    (atomGraph A.source a) realPoint invariant bipartite x y hxy

end
end CCO.AutomaticEPCore
