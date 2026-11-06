import CCO.ExactEPGeometry.ProjectedWords
import CCO.APCharacter.Towers.CurrentSource

/-!
# B062 C26/C28: original profiles along ACTUAL finite source histories

The accepted `CurrentSource.ActualStep` records a canonical source-to-source
`UnaryReduct` together with its genuine finite-age functor.  The accepted
`historyReduct` composes precisely these projections along an actual
finite history of successful AP-only steps.  Consequently the earlier
RAW word-forgetting lemmas can be applied DIRECTLY to a whole tower.

This is a real source-to-original, forward witness result.  It does not
assert reverse equality of current profiles with arbitrary old-word
traces, an arbitrary quotient SAP, or that a nominal unreleased step exists.
The source C23–C28 reverse trace/product lifting remains OPEN.
-/

universe u v w t

namespace CCO.ExactEPGeometry.ProjectedHistory

open APCharacter.Towers

variable {A B : CurrentSource.{u,v,w,t}}

/-- The ACTUAL composite original-reduct projection from a source
history, with each step already carrying a real implementation. -/
noncomputable abbrev projection
    (h : History (fun S T => Nonempty (CurrentSource.ActualStep S T)) A B) :
    UnaryReduct A.source B.source :=
  CurrentSource.historyReduct h

/-- Across the ENTIRE actual finite history, every current diversity
atom agrees exactly with its named old atom on the real projected pair. -/
theorem atom_iff
    (h : History (fun S T => Nonempty (CurrentSource.ActualStep S T)) A B)
    {i j : B.Sorts} (a : (B.source).Atom i j)
    (x : B.Point i) (y : B.Point j) :
    (B.source).atomRel a x y ↔
      (A.source).atomRel ((projection h).atom i j a)
        ((projection h).point i x) ((projection h).point j y) :=
  ProjectedWords.atom_iff A.source B.source (projection h) a x y

/-- Equality remains a genuine diagonal across any such actual tower:
the composite projection is injective on the WHOLE real carrier, hence
on every displayed current child. -/
theorem point_eq_iff
    (h : History (fun S T => Nonempty (CurrentSource.ActualStep S T)) A B)
    {i : B.Sorts} (x y : B.Point i) :
    (projection h).point i x = (projection h).point i y ↔ x = y :=
  ProjectedWords.point_eq_iff A.source B.source (projection h) x y

/-- C26 forward at arbitrary ACTUAL prefix length: the witness of a
current typed RAW word projects to a real original witness of its fully
typed forgotten word.  Every intermediate point is projected, not
chosen anew from an unrelated quotient section. -/
theorem word_forward
    (h : History (fun S T => Nonempty (CurrentSource.ActualStep S T)) A B)
    {i j : B.Sorts} (W : RawWord B.source i j)
    (x : B.Point i) (y : B.Point j)
    (hxy : RawWord.relation B.source W x y) :
    RawWord.relation A.source
      (ProjectedWords.forgetWord A.source B.source (projection h) W)
      ((projection h).point i x) ((projection h).point j y) :=
  ProjectedWords.forgetWord_forward A.source B.source (projection h) W x y hxy

/-- The finite conjunction of word restrictions is transported with
all of its REAL current witnesses. In particular the empty restriction
list remains the original RAW Top profile, never a fictitious identity
or a diversity-only profile. -/
theorem profile_forward
    (h : History (fun S T => Nonempty (CurrentSource.ActualStep S T)) A B)
    {i j : B.Sorts} (L : RawExact.Presentation B.source i j)
    (x : B.Point i) (y : B.Point j)
    (hxy : RawExact.evaluate B.source L x y) :
    RawExact.evaluate A.source
      (ProjectedWords.forgetProfile A.source B.source (projection h) L)
      ((projection h).point i x) ((projection h).point j y) :=
  ProjectedWords.forgetProfile_forward A.source B.source
    (projection h) L x y hxy

/-- Every current *nonempty* exact RAW presentation on a GENUINE
source-history terminal sort supplies a nonempty exact ORIGINAL
presentation. This theorem provides the forward source instance of the
C27 lift constructor for arbitrary accepted histories, without claiming
the converse current-trace equality. -/
theorem exact_forget
    (h : History (fun S T => Nonempty (CurrentSource.ActualStep S T)) A B)
    {i j : B.Sorts} (D : RawExact.NonemptyExact B.source i j) :
    ∃ E : RawExact.NonemptyExact A.source
        ((projection h).parent i) ((projection h).parent j),
      ∀ x : B.Point i, ∀ y : B.Point j,
        RawExact.evaluate B.source D.words x y →
        RawExact.evaluate A.source E.words
          ((projection h).point i x) ((projection h).point j y) := by
  refine ⟨ProjectedWords.forgetExact A.source B.source
    (projection h) D, ?_⟩
  intro x y hxy
  exact ProjectedWords.forgetExact_forward A.source B.source
    (projection h) D x y hxy

end CCO.ExactEPGeometry.ProjectedHistory
