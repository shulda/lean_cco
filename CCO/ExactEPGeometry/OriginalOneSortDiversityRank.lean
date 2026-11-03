import CCO.ExactEPGeometry.OriginalDiversityRank
import CCO.ExactEPGeometry.OriginalOneSortExactDescent

/-!
# B062 C106–C108: strict ORIGINAL rank for the actual canonical E quotient

For the ORIGINAL one-sort homogeneous source A, a strictly nonidentity
FULL RAW-exact original E contains a genuinely distinct pair x E y.
This witnesses collapse of an ACTUAL old diversity orbital. The
previous generic source-strength typed orbital-palette lemma applies
to the literal CanonicalTyped E quotient, with its genuine equivariant
quotient action; no artificial finite-index or quotient SAP premise.
The rank counts ORIGINAL diversity atoms, before safe unary labels.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- A genuinely nontrivial original full exact E strictly reduces the
original diversity-atom count on the ACTUAL one-original-sort E
quotient, without changing the original language or adding a
hypothetical quotient action section. -/
theorem originalOneSortExactQuotientDiversityRank_strict
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (hProper : (⊥ : ExactEq A.source base) < E) :
    let J := originalExactSourceKernelFamily A base hOne E
    let W := originalExactSourceKernelWords A base hOne E
    let hW := originalExactSourceKernelWords_relation A base hOne E
    let T := CCO.ExactCRT.CanonicalTyped.source
      A.source A.homogeneous J W hW
    Nat.card (T.Atom base base) < Nat.card (A.source.Atom base base) := by
  let J := originalExactSourceKernelFamily A base hOne E
  let W := originalExactSourceKernelWords A base hOne E
  let hW := originalExactSourceKernelWords_relation A base hOne E
  let Q := fun i : A.Sorts => Quotient (J i)
  letI : ∀ i : A.Sorts, MulAction A.G (Q i) :=
    CCO.ExactCRT.CanonicalTyped.action A.source A.homogeneous J W hW
  have hExist : ∃ x y : A.Point base, E x y ∧ x ≠ y := by
    by_contra hn
    apply hProper.not_ge
    intro x y hE
    by_contra hxy
    exact hn ⟨x,y,hE,hxy⟩
  have hJ : J base = E.val.val := by
    change (oldExactEqCast A.source (hOne base).symm E).val.val =
      E.val.val
    have hb : hOne base = rfl := Subsingleton.elim _ _
    rw [hb]
    rfl
  obtain ⟨x,y,hExy,hNe⟩ := hExist
  have hCollapsed : ∃ x y : A.Point base,
      x ≠ y ∧ (Quotient.mk'' x : Q base) = Quotient.mk'' y := by
    refine ⟨x,y,hNe,?_⟩
    apply Quotient.sound
    change (J base) x y
    rw [hJ]
    exact hExy
  have hRank := typedQuotientDiversityRank_strict_of_collapsed_pair
    A.source A.homogeneous Q id
      (fun _ => Quotient.mk'')
      (fun _ => Quotient.mk''_surjective)
      (fun i g x =>
        CCO.ExactCRT.CanonicalTyped.projection_equivariant
          A.source A.homogeneous J W hW i g x)
      base hCollapsed
  exact hRank

end
end CCO.ExactEPGeometry
