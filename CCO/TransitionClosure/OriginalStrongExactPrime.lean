import CCO.TransitionClosure.OriginalFullCoverInterpolation

/-!
# B049 source07 C19-C23: genuine original STRONG exact meet-primeness

At a nonzero full original meet-irreducible J with original full
cover K, assume the precise source positive presentations of J°
and K°. Suppose two NONEMPTY original STRONG exact same-sort
menus A,B have NONEMPTY intersection contained in J°. Then
at least one of A,B lies within J°.

The menus have finite original positive OLD word presentations;
the empty restriction family (real diversity Top) is retained.
If both menus exited J°, every defining word of either menu
would meet J° through one COMMON exact atom, and would exit J°
through its own menu's external witness. The already proved
original full-cover first-hit interpolation forces each such
word to meet the positive full K°\\J° layer. The ACCEPTED original
positive word Helly applied to all defining words plus the
ACTUAL positive old external-layer word yields an atom in
A∩B∩(K°\\J°), a contradiction.

No singleton restriction, nonempty defining-list hypothesis,
Set-Pasch, quotient/hidden SAP, artificial STRONG identity or
assumed prime property. Everything occurs in the original sort.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- SOURCE07 original strong-exact MI primality: genuine nonempty
exact menus A,B with nonempty meet inside J° cannot both exit J°.
Both original exact presentations may use EMPTY word lists (Top).
This is an unconditional original HOM/SAP/CCO source instance once
the source hypotheses of positivity J°, K° and FULL J⋖K are supplied.
-/
theorem original_full_MI_strong_exact_prime
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (J K : ColourEq S i)
    (hMI : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); InfIrred J)
    (hJK : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); J ⋖ K)
    (hJ : (⊥ : ColourEq S i) < J)
    (wJ wK : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J)
    (hwK : PositiveWord.profile S wK =
      originalEquivDiversityPalette S K)
    (A B : S.Menu i i)
    (hExactA : StrongExact.Exact S A)
    (hExactB : StrongExact.Exact S B)
    (hAB : (A ∩ B).Nonempty)
    (hInside : (A ∩ B) ⊆ originalEquivDiversityPalette S J) :
    A ⊆ originalEquivDiversityPalette S J ∨
      B ⊆ originalEquivDiversityPalette S J := by
  classical
  by_contra hNotPrime
  have hNotA : ¬ A ⊆ originalEquivDiversityPalette S J := by
    intro hA
    exact hNotPrime (Or.inl hA)
  have hNotB : ¬ B ⊆ originalEquivDiversityPalette S J := by
    intro hB
    exact hNotPrime (Or.inr hB)
  have hExitA : ∃ a : S.Atom i i,
      a ∈ A ∧ a ∉ originalEquivDiversityPalette S J := by
    by_contra hNone
    apply hNotA
    intro a ha
    by_contra hNotJ
    exact hNone ⟨a,ha,hNotJ⟩
  have hExitB : ∃ a : S.Atom i i,
      a ∈ B ∧ a ∉ originalEquivDiversityPalette S J := by
    by_contra hNone
    apply hNotB
    intro a ha
    by_contra hNotJ
    exact hNone ⟨a,ha,hNotJ⟩
  obtain ⟨aA,haA,hNotJaA⟩ := hExitA
  obtain ⟨aB,haB,hNotJaB⟩ := hExitB
  obtain ⟨c,hcA,hcB⟩ := hAB
  have hcJ : c ∈ originalEquivDiversityPalette S J :=
    hInside ⟨hcA,hcB⟩
  obtain ⟨_,wsA,hAeq⟩ := hExactA
  obtain ⟨_,wsB,hBeq⟩ := hExactB
  have hEachA : ∀ (a : S.Atom i i), a ∈ A →
      ∀ (word : PositiveWord S i i), word ∈ wsA →
        a ∈ PositiveWord.profile S word := by
    intro a ha word hWord
    have hPresented : a ∈ StrongExact.present S wsA := by
      rwa [← hAeq]
    exact hPresented word hWord
  have hEachB : ∀ (a : S.Atom i i), a ∈ B →
      ∀ (word : PositiveWord S i i), word ∈ wsB →
        a ∈ PositiveWord.profile S word := by
    intro a ha word hWord
    have hPresented : a ∈ StrongExact.present S wsB := by
      rwa [← hBeq]
    exact hPresented word hWord
  let ws : List (PositiveWord S i i) := wsA ++ wsB
  have hcWords : ∀ word ∈ ws, c ∈ PositiveWord.profile S word := by
    intro word hw
    rcases List.mem_append.mp hw with hwA | hwB
    · exact hEachA c hcA word hwA
    · exact hEachB c hcB word hwB
  have hWordExits : ∀ word ∈ ws,
      ∃ a : S.Atom i i,
        a ∈ PositiveWord.profile S word ∧
        a ∉ originalEquivDiversityPalette S J := by
    intro word hw
    rcases List.mem_append.mp hw with hwA | hwB
    · exact ⟨aA,hEachA aA haA word hwA,hNotJaA⟩
    · exact ⟨aB,hEachB aB haB word hwB,hNotJaB⟩
  have hWordLayer : ∀ word ∈ ws,
      (PositiveWord.profile S word ∩
        (originalEquivDiversityPalette S K \
          originalEquivDiversityPalette S J)).Nonempty := by
    intro word hw
    exact original_full_cover_positive_word_interpolation
      S H sap cco J K hMI hJK hJ wJ wK word hwJ hwK
        ⟨c,hcWords word hw,hcJ⟩ (hWordExits word hw)
  obtain ⟨wU,hwU⟩ :=
    original_full_cover_external_layer_positive_word
      S H sap cco J K hJK hJ wJ hwJ
  have hNotKLEJ : ¬ K ≤ J := not_le_of_gt hJK.1
  have hRealExternal : ∃ x y : X i, K x y ∧ ¬ J x y := by
    by_contra hNone
    apply hNotKLEJ
    intro x y hKxy
    by_contra hNotJ
    exact hNone ⟨x,y,hKxy,hNotJ⟩
  obtain ⟨x,y,hKxy,hNotJxy⟩ := hRealExternal
  have hxy : x ≠ y := by
    intro hEq
    subst y
    exact hNotJxy (J.val.refl x)
  have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
    intro hEq
    have hEqXY : x = y := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hEq
    exact hxy hEqXY
  obtain ⟨aU,haCol⟩ := S.some_colour_of_ne x y hTag
  have haUK : aU ∈ originalEquivDiversityPalette S K :=
    ⟨x,y,hKxy,haCol⟩
  have haUNotJ : aU ∉ originalEquivDiversityPalette S J := by
    rintro ⟨z,t,hJzt,hColZT⟩
    have hJxy : J x y :=
      (J.property z t x y (hColZT.trans haCol.symm)).mp hJzt
    exact hNotJxy hJxy
  have hUNonempty : (PositiveWord.profile S wU).Nonempty := by
    rw [hwU]
    exact ⟨aU,⟨haUK,haUNotJ⟩⟩
  let words : List (PositiveWord S i i) := ws ++ [wU]
  have hMembers : ∀ word : PositiveWord S i i,
      word ∈ words → word ∈ ws ∨ word = wU := by
    intro word hw
    change word ∈ ws ++ [wU] at hw
    rcases List.mem_append.mp hw with hBase | hSingleton
    · exact Or.inl hBase
    · exact Or.inr (by simpa using hSingleton)
  have hPair : StrongExact.PairwiseWordProfiles S words := by
    intro p hp q hq
    rcases hMembers p hp with hpW | rfl
    · rcases hMembers q hq with hqW | rfl
      · exact ⟨c,hcWords p hpW,hcWords q hqW⟩
      · obtain ⟨a,haP,haLayer⟩ := hWordLayer p hpW
        exact ⟨a,haP,by simpa only [hwU] using haLayer⟩
    · rcases hMembers q hq with hqW | rfl
      · obtain ⟨a,haQ,haLayer⟩ := hWordLayer q hqW
        exact ⟨a,by simpa only [hwU] using haLayer,haQ⟩
      · obtain ⟨a,ha⟩ := hUNonempty
        exact ⟨a,ha,ha⟩
  obtain ⟨d,hdWords⟩ :=
    original_positive_word_two_helly S H sap cco words hPair
  have hdA : d ∈ A := by
    rw [hAeq]
    intro word hw
    apply hdWords word
    change word ∈ ws ++ [wU]
    exact List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inl hw)))
  have hdB : d ∈ B := by
    rw [hBeq]
    intro word hw
    apply hdWords word
    change word ∈ ws ++ [wU]
    exact List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inr hw)))
  have hdU : d ∈ PositiveWord.profile S wU := by
    apply hdWords wU
    change wU ∈ ws ++ [wU]
    simp
  have hdLayer : d ∈ originalEquivDiversityPalette S K \
      originalEquivDiversityPalette S J := by
    rwa [hwU] at hdU
  exact hdLayer.2 (hInside ⟨hdA,hdB⟩)

end CCO.TransitionClosure
