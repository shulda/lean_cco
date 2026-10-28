import CCO.RawExact.LabelledRealTrace

/-!
# B002 C12/C18: no false equality edges in real RAW word walks

A represented RAW walk may revisit nonconsecutive real points,
but its consecutive diversity edges always join distinct TAGGED
real points. The proof does not postulate global injectivity, SAP
or any new mathematical provider. Reverse words have real
oppositely oriented witnesses, also when the original walk outputs
a logical diagonal.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Only adjacent tagged vertices are required to be distinct. -/
def SuccessiveDistinct : List (Sigma X) → Prop
  | [] => True
  | [_] => True
  | p :: q :: tail => p ≠ q ∧ SuccessiveDistinct (q :: tail)

/-- A coloured old walk has no artificial equality-labelled
edge, although distant formal vertices may have equal images. -/
theorem certifiedWalk_successiveDistinct
    {points : List (Sigma X)}
    {atoms : List (TypedAtomicStep S)}
    (h : TypedWalkCertificate S points atoms) :
    SuccessiveDistinct points := by
  induction h with
  | singleton p => trivial
  | step x y a edge rest ih =>
      exact ⟨S.atomRel_ne edge, ih⟩

theorem actualWordPath_successiveDistinct
    {i j : ι} {word : RawWord S i j}
    {x : X i} {z : X j}
    (path : WordPath S word x z) :
    SuccessiveDistinct (realWalkTrace S path) :=
  certifiedWalk_successiveDistinct S
    (realWalkTrace_certified S path)

/-- A genuine RAW word reversed to the correct opposite
typed endpoint direction has a real witness. -/
theorem realWordPath_converse
    {i j : ι} (word : RawWord S i j)
    (x : X i) (y : X j)
    (path : WordPath S word x y) :
    Nonempty (WordPath S (RawWord.reverse S word) y x) := by
  apply (wordPath_iff_relation S (RawWord.reverse S word) y x).mpr
  rw [RawWord.relation_reverse S]
  exact (wordPath_iff_relation S word x y).mp ⟨path⟩

end CCO.RawExact
