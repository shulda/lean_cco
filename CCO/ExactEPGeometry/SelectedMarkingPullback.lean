import CCO.RigidGroupoid.Phase.AbstractMarkings
import Mathlib.Tactic.Abel

/-!
# B062 C93: source-level character marking pullback under ACTUAL action maps

If an old groupoid action is transported to a selected groupoid
action on genuine points, preserving every full-arrow action
and the corrected character, then EVERY global selected marking
pulls back to a compatible old marking after the objectwise
ZMod 2 correction. This pure algebraic lemma verifies ALL arrows,
not merely a generating subfamily, and it treats repeated or
merged objects without choosing a new point-action section.

In B062 the naturality maps and corrected-character identity MUST
still be instantiated from the actual original E-occupancy quotient,
C83 full Arrow correspondences and C79/C84 original gates. The
generic theorem is not a conditional completion of that instance.
-/

universe u v w x y z

namespace CCO.ExactEPGeometry

open CategoryTheory
open CCO.RigidGroupoid.Phase

noncomputable section

/-- A selected full-character marking pulls back along any genuine
arrow-natural action map with a precisely corrected character.
No bijectivity of the point maps or quotient SAP is required;
naturality on EVERY complete Arrow is the explicit obligation. -/
theorem selectedMarkingPullback
    {J : Type u} [Groupoid.{v} J]
    {K : Type x} [Groupoid.{y} K]
    (F : J ⥤ Type w) (Q : K ⥤ Type z)
    (chi : Abstract.Character J) (chiQ : Abstract.Character K)
    (owner : J → K)
    (mapArrow : ∀ {a b : J}, (a ⟶ b) → (owner a ⟶ owner b))
    (mapPoint : ∀ a : J, F.obj a → Q.obj (owner a))
    (gamma : J → ZMod 2)
    (hNatural : ∀ {a b : J} (R : a ⟶ b) (p : F.obj a),
      mapPoint b (F.map R p) =
        Q.map (mapArrow R) (mapPoint a p))
    (hCharacter : ∀ {a b : J} (R : a ⟶ b),
      chiQ.value (mapArrow R) =
        gamma a + chi.value R + gamma b)
    (mark : Abstract.Point Q → ZMod 2)
    (hMark : Abstract.IsMarking Q chiQ mark) :
    Abstract.IsMarking F chi
      (fun p => mark ⟨owner p.1, mapPoint p.1 p.2⟩ + gamma p.1) := by
  intro a b R p
  change mark ⟨owner b,mapPoint b (F.map R p)⟩ + gamma b =
    (mark ⟨owner a,mapPoint a p⟩ + gamma a) + chi.value R
  rw [hNatural R p]
  have hSelected := hMark (mapArrow R) (mapPoint a p)
  rw [hSelected,hCharacter]
  have hDouble : gamma b + gamma b = 0 := by
    have hh : ∀ d : ZMod 2, d + d = 0 := by decide
    exact hh _
  calc
    (mark ⟨owner a,mapPoint a p⟩ +
        (gamma a + chi.value R + gamma b)) + gamma b =
      ((mark ⟨owner a,mapPoint a p⟩ + gamma a) +
        chi.value R) + (gamma b + gamma b) := by abel
    _ = (mark ⟨owner a,mapPoint a p⟩ + gamma a) +
        chi.value R := by rw [hDouble,add_zero]

end
end CCO.ExactEPGeometry
