import CCO.TerminalLattice.OriginalStrongAlgebra
import CCO.StrongExact.ProfileSemantics
import CCO.RawWords

/-!
# B050 C26: two original private positive-word branches form a legal cycle

The two different private branches of a source theta gadget can share
an assigned nonempty OLD diversity menu D in their STRONG endpoint
spectra. An actual original fine atom d in D is realized by each
branch at distinct endpoints, by accepted B001 original SAP guarded
word semantics. ORIGINAL pair homogeneity aligns the two pairs with
the same old colour, with one *full* old G element.

The result is an actual homomorphic realization of the whole
two-branch closed RAW cycle (not necessarily an injective embedding
of interior vertices), preserving all prescribed original named sorts
of both words. It does NOT assert feasibility of arbitrary graph
cycles or one global original CCO completion; those remain C27–C34.
No quotient homogeneity or synthetic STRONG identity is used.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Two actual OLD positive atomic-word branches whose profiles contain
the SAME nonempty diversity menu have a common real endpoint pair
realizing both complete typed represented walks. In particular these
endpoints are genuinely distinct as tagged old points. -/
theorem original_two_positive_branches_common_real_pair
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (D : S.Menu i j) (hD : D.Nonempty)
    (first second : PositiveWord S i j)
    (hFirst : D ⊆ PositiveWord.profile S first)
    (hSecond : D ⊆ PositiveWord.profile S second) :
    ∃ x : X i, ∃ y : X j,
      PositiveWord.represented S first x y ∧
      PositiveWord.represented S second x y ∧
      (⟨i,x⟩ : Sigma X) ≠ ⟨j,y⟩ := by
  obtain ⟨d, hd⟩ := hD
  obtain ⟨x, y, hFirstXY, hColourXY⟩ :=
    (StrongExact.positive_profile_iff_represented S H sap first d).mp
      (hFirst hd)
  obtain ⟨u, v, hSecondUV, hColourUV⟩ :=
    (StrongExact.positive_profile_iff_represented S H sap second d).mp
      (hSecond hd)
  obtain ⟨g, hgu, hgv⟩ :=
    S.pair_homogeneous_of_homogeneous H u x v y
      (hColourUV.trans hColourXY.symm)
  have hMoved : PositiveWord.represented S second (g • u) (g • v) :=
    (PositiveWord.represented_invariant_of_homogeneous S H second)
      g u v hSecondUV
  have hSecondXY : PositiveWord.represented S second x y := by
    simpa only [hgu, hgv] using hMoved
  have hTagged : (⟨i,x⟩ : Sigma X) ≠ ⟨j,y⟩ := by
    intro heq
    have hn : S.colour x y = none :=
      (S.colour_none_iff x y).mpr heq
    rw [hn] at hColourXY
    cases hColourXY
  exact ⟨x,y,hFirstXY,hSecondXY,hTagged⟩

/-- C26 actual whole two-branch OLD simple-cycle homomorphism, expressed
as the represented closed RAW word consisting of the first positive
branch and the reversal of the second. Both positive words retain all
their actual named-sort intermediate atoms; the conclusion permits
homomorphic collisions in unprescribed nonadjacent vertices exactly
as source homomorphic-CCO does. -/
theorem original_two_positive_branches_closed_walk
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (D : S.Menu i j) (hD : D.Nonempty)
    (first second : PositiveWord S i j)
    (hFirst : D ⊆ PositiveWord.profile S first)
    (hSecond : D ⊆ PositiveWord.profile S second) :
    ∃ x : X i,
      RawWord.relation S
        (RawWord.append S
          (PositiveWord.toRawWord S first)
          (RawWord.reverse S (PositiveWord.toRawWord S second)))
        x x := by
  obtain ⟨x,y,hFirstXY,hSecondXY,_⟩ :=
    original_two_positive_branches_common_real_pair
      S H sap D hD first second hFirst hSecond
  refine ⟨x, ?_⟩
  rw [RawWord.relation_append S, RawWord.relation_reverse S]
  refine ⟨y, ?_, ?_⟩
  · rw [← PositiveWord.represented_toRawWord S first]
    exact hFirstXY
  · change RawWord.relation S (PositiveWord.toRawWord S second) x y
    rw [← PositiveWord.represented_toRawWord S second]
    exact hSecondXY

end CCO.TerminalLattice
