import CCO.ParityHasse.Original.SourceHasse
import CCO.PositiveWords

/-! Original-source orbital parity with its separate, visible-SAP STRONG
upgrade. The even relation remains equality-inclusive; only its diversity
slice is a STRONG profile. No SAP is transported to an abstract quotient. -/
universe u v w t
namespace CCO.OrbitalCover
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- C03: actual two-point SAP gluing supplies distinct even endpoints.
This lemma needs no CCO, finite interval or bipartiteness. -/
theorem even_diversity_nonempty (H : HomogeneousSource S G)
    (sap : AgeSAP S) (c : S.Atom i i) :
    ∃ x y : X i, x ≠ y ∧ EvenWalk (S.atomRel c) x y := by
  obtain ⟨d,x,z,y,hxz,hzy,hxy⟩ := S.realPointGluing_of_SAP H sap c c
  refine ⟨x,y,?_,2,even_two,z,hxz,y,hzy,rfl⟩
  intro h
  subst y
  change S.colour x x = some d at hxy
  have hn := (S.colour_none_iff x x).mpr rfl
  rw [hn] at hxy
  cases hxy

/-- Literal nonempty repeated old diversity word, of length n+1. -/
def positivePower (c : S.Atom i i) : Nat → PositiveWord S i i
  | 0 => .single c
  | n+1 => .cons c (positivePower c n)

theorem positivePower_represented (c : S.Atom i i) (n : Nat) :
    PositiveWord.represented S (positivePower S c n) =
      relPow (S.atomRel c) (n+1) := by
  induction n with
  | zero =>
    funext x y
    exact propext (relPow_one (S.atomRel c) x y).symm
  | succ n ih =>
    change TRel.comp (S.atomRel c)
      (PositiveWord.represented S (positivePower S c n)) = _
    rw [ih]
    rfl

/-- C02/C04: stabilized even/odd RAW relations have nonempty STRONG
diversity profiles under original SAP. The even RAW relation itself has
not been replaced by a diversity palette. -/
theorem strong_parity_profiles (H : HomogeneousSource S G)
    (sap : AgeSAP S) (c : S.Atom i i) :
    ∃ N : Nat, 0 < N ∧ ∃ even odd : PositiveWord S i i,
      (∀ x y, evenColourEq S H c x y ↔
        PositiveWord.represented S even x y) ∧
      (∀ x y, OddWalk (S.atomRel c) x y ↔
        PositiveWord.represented S odd x y) ∧
      S.diversityGuard (evenColourEq S H c) = PositiveWord.profile S even ∧
      S.diversityGuard (OddWalk (S.atomRel c)) = PositiveWord.profile S odd ∧
      (PositiveWord.profile S even).Nonempty ∧
      (PositiveWord.profile S odd).Nonempty := by
  obtain ⟨N,hN,he,ho⟩ := parity_profiles_positive_raw S H c
  let even := positivePower S c (2*N-1)
  let odd := positivePower S c (2*N)
  have heq : PositiveWord.represented S even =
      RawWord.relation S (atomWord S c (2*N)) := by
    rw [atomWord_relation]
    dsimp [even]
    rw [positivePower_represented]
    congr 1
    omega
  have hoq : PositiveWord.represented S odd =
      RawWord.relation S (atomWord S c (2*N+1)) := by
    rw [atomWord_relation]
    exact positivePower_represented S c (2*N)
  have hEven : (evenColourEq S H c : X i → X i → Prop) =
      PositiveWord.represented S even := by
    funext x y
    exact propext ((he x y).trans (by rw [heq]))
  have hOdd : OddWalk (S.atomRel c) = PositiveWord.represented S odd := by
    funext x y
    exact propext ((ho x y).trans (by rw [hoq]))
  refine ⟨N,hN,even,odd,?_,?_,?_,?_,?_,?_⟩
  · intro x y; rw [hEven]
  · intro x y; rw [hOdd]
  · rw [hEven]
    exact PositiveWord.diversityGuard_represented_eq_profile_of_SAP S H sap even
  · rw [hOdd]
    exact PositiveWord.diversityGuard_represented_eq_profile_of_SAP S H sap odd
  · exact PositiveWord.profile_nonempty_of_SAP S H sap even
  · exact PositiveWord.profile_nonempty_of_SAP S H sap odd

/-- C01–C06, `thm:orbital-parity`: original SAP-free parity and positive
RAW exactness, together with the additional visible-SAP diversity result.
The general source parity theorem keeps its separate SAP-free signature. -/
theorem orbital_parity (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S) (sap : AgeSAP S)
    (E F : ColourEq S i) (a : X i)
    [Finite (RelativeClass E.val F.val a)] (c : S.Atom i i)
    (hFE : ∀ x y, S.atomRel c x y → F x y ∧ ¬ E x y) :
    evenColourEq S H c ⋖ connectivityColourEq S H c ∧
    relativeIndex (evenColourEq S H c).val
      (connectivityColourEq S H c).val a = 2 ∧
    connectivityColourEq S H c ≤ F ∧
    ¬ connectivityColourEq S H c ≤ E ∧
    (∃ Y O : RawExact.NonemptyExact S i i,
      (∀ x y, RawExact.evaluate S Y.words x y ↔ evenColourEq S H c x y) ∧
      (∀ x y, RawExact.evaluate S O.words x y ↔ OddWalk (S.atomRel c) x y)) ∧
    (∃ x y : X i, x ≠ y ∧ evenColourEq S H c x y) ∧
    (∃ even odd : PositiveWord S i i,
      S.diversityGuard (evenColourEq S H c) = PositiveWord.profile S even ∧
      S.diversityGuard (OddWalk (S.atomRel c)) = PositiveWord.profile S odd ∧
      (PositiveWord.profile S even).Nonempty ∧
      (PositiveWord.profile S odd).Nonempty) := by
  obtain ⟨hcov,hidx,hF,hE,_,_⟩ := source_orbital_parity S H cco E F a c hFE
  obtain ⟨N,hN,even,odd,_,_,he,ho,hne,hno⟩ := strong_parity_profiles S H sap c
  exact ⟨hcov,hidx,hF,hE,parity_profiles_nonempty_exact S H c,
    even_diversity_nonempty S H sap c,even,odd,he,ho,hne,hno⟩

end CCO.OrbitalCover
