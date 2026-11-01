import CCO.TransitionClosure.OriginalFirstHitPeirce
import CCO.TerminalLattice.OriginalFullExternalLayer
import Mathlib.Tactic.FinCases

/-!
# B049 source07 C17: genuinely positive original quotient first-hit profiles

The quotient state of an ORIGINAL positive word, saturated by the
positive nonzero old J-diversity word, itself has ONE concrete positive
OLD typed word profile. Its genuine quotient powers are positive by
the source09 old-SAP quotient semigroup, including quotient diagonal.

A reusable three-state Helly consequence explicitly invokes the
source09 finite-state theorem, whose provider proves it from ORIGINAL
positive OLD word Helly, original CCO and old SAP. No quotient CCO,
hidden SAP, arbitrary exact-PC product or invented external layer.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- The real old J-saturated state of one positive original word
is itself positive in the EXACT quotient sense, including all true
J-quotient diagonal edges (whose old pullback remains diversity).
The concrete word is wJ appended to wP and wJ, with actual SAP
discharging STRONG word concatenation. -/
theorem originalJMenuQuotientState_positive
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (wJ wP : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J) :
    OriginalPositiveQuotientState S J
      (originalJMenuQuotientState S J (PositiveWord.profile S wP)) := by
  let R : X i → X i → Prop :=
    quotientDiversity J.val
      (originalJMenuQuotientState S J (PositiveWord.profile S wP))
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  have hColor : ColourInvariant S i R := by
    apply groupInvariant_colourInvariant S H
    intro g x y hxy
    refine ⟨?_, ?_⟩
    · intro hEq
      exact hxy.1 (smul_left_cancel g hEq)
    · have hMove :=
        originalJMenuQuotientState_groupInvariant S H J
          (PositiveWord.profile S wP) g
          (Quotient.mk J.val x) (Quotient.mk J.val y) hxy.2
      simpa only [originalQuotient_mk_smul S H J] using hMove
  have hDiv : ∀ x y : X i, R x y → x ≠ y :=
    fun _ _ h => h.1
  refine ⟨originalJPositiveSaturationWord S wJ wP, ?_⟩
  rw [originalJPositiveSaturationWord_quotient_profile
    S H sap J hJ wJ wP hwJ]
  change S.menuRel (S.diversityGuard R) = R
  exact menuRel_diversityGuard_of_colourInvariant S R hColor hDiv

/-- Every POSITIVE genuine old quotient state R has an ORIGINAL
positive typed word for its true R^(n+1) relation. The first
power is R itself; all later powers use the already proved
actual old SAP quotient semigroup. In particular the first-hit
Abar=Sbar^(n-1) is not a new positive-word assumption. -/
theorem original_positive_quotient_state_relPow_succ
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (R : Quotient J.val → Quotient J.val → Prop)
    (hR : OriginalPositiveQuotientState S J R) :
    ∀ n : Nat,
      OriginalPositiveQuotientState S J (relPow R (n+1)) := by
  intro n
  induction n with
  | zero =>
      obtain ⟨w,hw⟩ := hR
      refine ⟨w, ?_⟩
      calc
        S.menuRel (PositiveWord.profile S w) =
            quotientDiversity J.val R := hw
        _ = quotientDiversity J.val (relPow R 1) := by
          congr 1
          funext q r
          apply propext
          exact (relPow_one R q r).symm
  | succ n ih =>
      change OriginalPositiveQuotientState S J
        (RawSymmetric.compose R (relPow R (n+1)))
      exact original_positive_quotient_state_comp
        S H sap J hJ R (relPow R (n+1)) hR ih

/-- Source07 three-profile Helly, with the actual quotients allowed
to have TRUE diagonal pairs. All three state-word presentations must
be genuine original OLD positive paths, and finite Helly is discharged
by the ACCEPTED B050 source theorem, itself proved from old CCO/SAP. -/
theorem original_three_positive_quotient_states_helly
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (R T U : Quotient J.val → Quotient J.val → Prop)
    (hR : OriginalPositiveQuotientState S J R)
    (hT : OriginalPositiveQuotientState S J T)
    (hU : OriginalPositiveQuotientState S J U)
    (hRT : ∃ q r : Quotient J.val, R q r ∧ T q r)
    (hRU : ∃ q r : Quotient J.val, R q r ∧ U q r)
    (hTU : ∃ q r : Quotient J.val, T q r ∧ U q r) :
    ∃ q r : Quotient J.val, R q r ∧ T q r ∧ U q r := by
  classical
  obtain ⟨wR,hwR⟩ := hR
  obtain ⟨wT,hwT⟩ := hT
  obtain ⟨wU,hwU⟩ := hU
  let states : Fin 3 → Quotient J.val → Quotient J.val → Prop :=
    Fin.cons R (Fin.cons T (Fin.cons U Fin.elim0))
  let words : Fin 3 → PositiveWord S i i :=
    Fin.cons wR (Fin.cons wT (Fin.cons wU Fin.elim0))
  have hWords : ∀ k : Fin 3,
      S.menuRel (PositiveWord.profile S (words k)) =
        quotientDiversity J.val (states k) := by
    intro k
    induction k using Fin.cases with
    | zero =>
        simpa only [words, states, Fin.cons_zero] using hwR
    | succ j =>
        induction j using Fin.cases with
        | zero =>
            simpa only [words, states, Fin.cons_succ, Fin.cons_zero] using hwT
        | succ z =>
            induction z using Fin.cases with
            | zero =>
                simpa only [words, states, Fin.cons_succ, Fin.cons_zero] using hwU
            | succ impossible =>
                exact Fin.elim0 impossible
  obtain ⟨qRT,rRT,hRrt,hTrt⟩ := hRT
  obtain ⟨qRU,rRU,hRru,hUru⟩ := hRU
  obtain ⟨qTU,rTU,hTtu,hUtu⟩ := hTU
  have hRR : ∃ q r : Quotient J.val, R q r ∧ R q r :=
    ⟨qRT,rRT,hRrt,hRrt⟩
  have hTT : ∃ q r : Quotient J.val, T q r ∧ T q r :=
    ⟨qRT,rRT,hTrt,hTrt⟩
  have hUU : ∃ q r : Quotient J.val, U q r ∧ U q r :=
    ⟨qRU,rRU,hUru,hUru⟩
  have hTR : ∃ q r : Quotient J.val, T q r ∧ R q r :=
    ⟨qRT,rRT,hTrt,hRrt⟩
  have hUR : ∃ q r : Quotient J.val, U q r ∧ R q r :=
    ⟨qRU,rRU,hUru,hRru⟩
  have hUT : ∃ q r : Quotient J.val, U q r ∧ T q r :=
    ⟨qTU,rTU,hUtu,hTtu⟩
  have hPair : ∀ k l : Fin 3,
      ∃ q r : Quotient J.val, states k q r ∧ states l q r := by
    intro k l
    fin_cases k <;> fin_cases l <;>
      simp only [states, Fin.cons_zero, Fin.cons_succ] <;>
      first
      | exact hRR
      | exact ⟨qRT,rRT,hRrt,hTrt⟩
      | exact ⟨qRU,rRU,hRru,hUru⟩
      | exact hTR
      | exact hTT
      | exact ⟨qTU,rTU,hTtu,hUtu⟩
      | exact hUR
      | exact hUT
      | exact hUU
  obtain ⟨q,r,hAll⟩ :=
    original_positive_quotient_states_finite_helly
      S H sap cco J hJ states words hWords hPair
  refine ⟨q,r,?_,?_,?_⟩
  · simpa [states] using hAll 0
  · simpa [states] using hAll 1
  · have hTwo : (2 : Fin 3) = Fin.succ (Fin.succ (0 : Fin 1)) := by decide
    simpa only [hTwo, states, Fin.cons_succ, Fin.cons_zero] using hAll 2

end CCO.TransitionClosure
