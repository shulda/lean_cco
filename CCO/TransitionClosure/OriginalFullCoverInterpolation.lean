import CCO.TransitionClosure.OriginalFirstHitPositive

/-!
# B049 source07 C17-C18: ORIGINAL full-cover first-hit interpolation (OWI)

This is the actual positive-old-word theorem at one LOCAL FULL original
meet-irreducible J with FULL cover K. We assume precisely its stipulated
old positive presentations of J-diversity, K-diversity and the tested P,
plus genuine P meeting J and exiting J. There is no terminal NR2, no
represented-lattice substitution, no hidden/quotient SAP or CCO, and
no exact-domain or Set-Pasch product.

If P missed K\J, the previous files construct a least real Sbar-power
hitting the K/J external layer and prove exact intersections:
 Abar ∩ K/J = Delta, (Sbar;Ubar) ∩ K/J = Ubar,
 and Abar ∩ (Sbar;Ubar) is nonempty.
The three quotient states are OLD positive-word states, with Abar
obtained by actual quotient semigroup induction and Ubar by the
already ACCEPTED B050 independently proved original layer word.
Original CCO+SAP positive Helly makes their triple intersection
nonempty, contradicting disjointness of Delta and Ubar.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- SOURCE07 selected ORIGINAL OWI:
on ONE original named sort, with Id<J⋖K in the actual FULL
invariant-equivalence lattice and J truly meet-irreducible,
every positive OLD typed word P whose diversity profile meets
J° but exits J must also meet the FULL external layer K°\J°.

All of wJ, wK, wP are ACTUAL positive original typed words;
their interior sorts are arbitrary original sorts. Source-level
SAP and homomorphic CCO (not quotient SAP/CCO) discharge every
word/power/Helly obligation. The separately proved source09
full external-layer positive provider is consumed, not assumed.
-/
theorem original_full_cover_positive_word_interpolation
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (J K : ColourEq S i)
    (hMI : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); InfIrred J)
    (hJK : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); J ⋖ K)
    (hJ : (⊥ : ColourEq S i) < J)
    (wJ wK wP : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J)
    (hwK : PositiveWord.profile S wK =
      originalEquivDiversityPalette S K)
    (hMeet : (PositiveWord.profile S wP ∩
      originalEquivDiversityPalette S J).Nonempty)
    (hExit : ∃ a : S.Atom i i,
      a ∈ PositiveWord.profile S wP ∧
      a ∉ originalEquivDiversityPalette S J) :
    (PositiveWord.profile S wP ∩
      (originalEquivDiversityPalette S K \
        originalEquivDiversityPalette S J)).Nonempty := by
  classical
  let P : S.Menu i i := PositiveWord.profile S wP
  by_contra hMissing
  have hAvoid : ∀ a : S.Atom i i,
      a ∈ P →
      a ∈ originalEquivDiversityPalette S K →
      a ∈ originalEquivDiversityPalette S J := by
    intro a ha hKa
    by_contra hNotJ
    exact hMissing ⟨a,ha,⟨hKa,hNotJ⟩⟩
  obtain ⟨n,hn,hA,hT,hAT⟩ :=
    originalJMenuQuotientState_first_hit_K_geometry
      S H J K hMI hJK P hMeet hExit hAvoid
  let R : Quotient J.val → Quotient J.val → Prop :=
    originalJMenuQuotientState S J P
  let U : Quotient J.val → Quotient J.val → Prop :=
    originalQuotientExternalLayer S J K hJK.1.le
  let V : Quotient J.val → Quotient J.val → Prop :=
    (originalUpperSetoid S J K hJK.1.le).r
  let A : Quotient J.val → Quotient J.val → Prop := relPow R (n-1)
  let T : Quotient J.val → Quotient J.val → Prop :=
    RawSymmetric.compose R U
  have hPosR : OriginalPositiveQuotientState S J R :=
    originalJMenuQuotientState_positive S H sap J hJ wJ wP hwJ
  have hPosA : OriginalPositiveQuotientState S J A := by
    have hPowers := original_positive_quotient_state_relPow_succ
      S H sap J hJ R hPosR (n-2)
    have hExponent : n-1 = (n-2)+1 := by omega
    change OriginalPositiveQuotientState S J (relPow R (n-1))
    rw [hExponent]
    exact hPowers
  have hPosU : OriginalPositiveQuotientState S J U := by
    obtain ⟨wU, hwU⟩ :=
      original_full_cover_external_layer_positive_word
        S H sap cco J K hJK hJ wJ hwJ
    refine ⟨wU, ?_⟩
    change S.menuRel (PositiveWord.profile S wU) =
      quotientDiversity J.val (originalQuotientExternalLayer S J K hJK.1.le)
    rw [hwU]
    exact original_external_layer_fine_menu_semantics S J K hJK.1.le
  have hPosT : OriginalPositiveQuotientState S J T :=
    original_positive_quotient_state_comp
      S H sap J hJ R U hPosR hPosU
  have hPosV : OriginalPositiveQuotientState S J V := by
    refine ⟨wK, ?_⟩
    rw [hwK, originalEquivDiversityPalette_semantics S K]
    funext x y
    apply propext
    constructor
    · rintro ⟨hxy,hKxy⟩
      exact ⟨hxy,(originalUpperSetoid_mk S J K hJK.1.le x y).mpr hKxy⟩
    · rintro ⟨hxy,hUpper⟩
      exact ⟨hxy,(originalUpperSetoid_mk S J K hJK.1.le x y).mp hUpper⟩
  have hAT' : ∃ q r : Quotient J.val, A q r ∧ T q r := hAT
  have hAV : ∃ q r : Quotient J.val, A q r ∧ V q r := by
    obtain ⟨q,_,_,_⟩ := hAT'
    refine ⟨q,q,?_,?_⟩
    · exact originalJMenuQuotientState_power_diagonal
        S H J P hMeet (n-1) q
    · exact (originalUpperSetoid S J K hJK.1.le).refl q
  have hNotLE : ¬ K ≤ J := not_le_of_gt hJK.1
  have hKpair : ∃ x y : X i, K x y ∧ ¬ J x y := by
    by_contra hNone
    apply hNotLE
    intro x y hKxy
    by_contra hNotJ
    exact hNone ⟨x,y,hKxy,hNotJ⟩
  obtain ⟨x,y,hKxy,hNotJxy⟩ := hKpair
  have hTV : ∃ q r : Quotient J.val, T q r ∧ V q r := by
    let q : Quotient J.val := Quotient.mk J.val x
    let r : Quotient J.val := Quotient.mk J.val y
    have hUqr : U q r := by
      refine ⟨(originalUpperSetoid_mk S J K hJK.1.le x y).mpr hKxy, ?_⟩
      intro hEq
      exact hNotJxy (Quotient.exact hEq)
    refine ⟨q,r,?_,hUqr.1⟩
    exact ⟨q, originalJMenuQuotientState_contains_diagonal
      S H J P hMeet q, hUqr⟩
  obtain ⟨q,r,hAqr,hTqr,hVqr⟩ :=
    original_three_positive_quotient_states_helly
      S H sap cco J hJ A T V hPosA hPosT hPosV hAT' hAV hTV
  have hEq : q = r := (hA q r hVqr).mp hAqr
  have hExternal : U q r := (hT q r hVqr).mp hTqr
  exact hExternal.2 hEq

end CCO.TransitionClosure
