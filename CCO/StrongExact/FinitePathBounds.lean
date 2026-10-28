import CCO.StrongExact.PathCycleSupport
import CCO.StrongExact.ExactMenus

/-!
# C13: finite exact presentation of the complete positive-path bound

Although a finite partial diagram can admit infinitely many
endpoint-separated walks, their STRONG profiles range over the
FINITE Boolean diversity palette of the ordered endpoint sorts.
Choose one genuinely positive word for each distinct occurring
profile. Their finite intersection is exactly the original
all-positive-path bound, including the no-path/typed-Top case.

This is a new unconditional combinatorial exactness lemma:
nonempty all-path bounds are in the ORIGINAL exact family, with
NO assumption of theta Helly, semantic CCO, SAP, or PC completeness.
It is NOT the converse C12 PC walk formula; equality of the bound
with the PC fixed network remains to be proved separately.
-/

universe u v w z

namespace CCO.StrongPC

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u, v, w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

/-- Every set of endpoint-separated specified walks has only finitely
many distinct STRONG menus because its literal endpoint diversity
atom palette is finite. Thus the intersection of all its profiles
admits a finite list presentation by ACTUAL positive words. -/
theorem positivePathBound_has_finite_presentation (x y : V) :
    ∃ words : List (PositiveWord S (D.vertexSort x) (D.vertexSort y)),
      positivePathBound D x y = StrongExact.present S words := by
  classical
  letI : Fintype (S.Atom (D.vertexSort x) (D.vertexSort y)) :=
    S.finiteAtom _ _
  haveI : Finite (S.Menu (D.vertexSort x) (D.vertexSort y)) := by
    infer_instance
  letI : Fintype (S.Menu (D.vertexSort x) (D.vertexSort y)) :=
    Fintype.ofFinite _
  let candidates : List (S.Menu (D.vertexSort x) (D.vertexSort y)) :=
    (Finset.univ : Finset (S.Menu (D.vertexSort x) (D.vertexSort y))).toList
  let representative (m : S.Menu (D.vertexSort x) (D.vertexSort y)) :
      List (PositiveWord S (D.vertexSort x) (D.vertexSort y)) :=
    if h : ∃ p : SpecifiedPath D x y,
        PositiveWord.profile S p.word = m then
      [(Classical.choose h).word]
    else []
  let words := candidates.flatMap representative
  refine ⟨words, ?_⟩
  ext a
  constructor
  · intro ha
    change ∀ p : SpecifiedPath D x y,
      a ∈ PositiveWord.profile S p.word at ha
    change ∀ w ∈ words, a ∈ PositiveWord.profile S w
    intro w hw
    obtain ⟨m, hm, hrep⟩ := List.mem_flatMap.mp hw
    by_cases hex : ∃ p : SpecifiedPath D x y,
        PositiveWord.profile S p.word = m
    · have hwEq : w = (Classical.choose hex).word := by
        simpa [representative, hex] using hrep
      subst w
      exact ha (Classical.choose hex)
    · have hFalse : False := by
        simpa [representative, hex] using hrep
      exact False.elim hFalse
  · intro ha
    change ∀ w ∈ words, a ∈ PositiveWord.profile S w at ha
    change ∀ p : SpecifiedPath D x y,
      a ∈ PositiveWord.profile S p.word
    intro p
    let m : S.Menu (D.vertexSort x) (D.vertexSort y) :=
      PositiveWord.profile S p.word
    have hex : ∃ q : SpecifiedPath D x y,
        PositiveWord.profile S q.word = m := ⟨p, rfl⟩
    have hm : m ∈ candidates := by
      simp [candidates]
    have hrepresentative :
        (Classical.choose hex).word ∈ representative m := by
      simp [representative, hex]
    have hselected :
        (Classical.choose hex).word ∈ words :=
      List.mem_flatMap.mpr ⟨m, hm, hrepresentative⟩
    have hvalue := ha (Classical.choose hex).word hselected
    have hmEq :
        PositiveWord.profile S (Classical.choose hex).word = m :=
      Classical.choose_spec hex
    rw [hmEq] at hvalue
    exact hvalue

/-- C13 exact-family partial inclusion, without CCO: any *nonempty*
complete positive-path bound is an actual finite meet of positive
STRONG word profiles, even when cycles give infinitely many walks. -/
theorem positivePathBound_exact_of_nonempty
    (x y : V) (hne : (positivePathBound D x y).Nonempty) :
    StrongExact.Exact S (positivePathBound D x y) := by
  obtain ⟨ws, hws⟩ :=
    positivePathBound_has_finite_presentation D x y
  exact ⟨hne, ws, hws⟩

/-- Boundary: if there is no specified positive path, the endpoint
bound is the full typed diversity Top, not a diagonal identity. -/
theorem positivePathBound_eq_top_of_no_paths
    (x y : V) (hNo : IsEmpty (SpecifiedPath D x y)) :
    positivePathBound D x y =
      (Set.univ : S.Menu (D.vertexSort x) (D.vertexSort y)) := by
  letI : IsEmpty (SpecifiedPath D x y) := hNo
  ext a
  constructor
  · intro _
    exact Set.mem_univ a
  · intro _
    intro p
    exact isEmptyElim p

end CCO.StrongPC
