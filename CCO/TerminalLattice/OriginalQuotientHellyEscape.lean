import CCO.TerminalLattice.OriginalExternalQuotientStates
import CCO.TerminalLattice.OriginalQuotientOWLIntersection
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# B050 source09 OWL: one genuine positive finite-state escape by old CCO+SAP

Suppose for contradiction that no product of two DISTINCT complete
external original-G quotient orbitals covers the whole K/J external
layer. The already proved exact OWL-I intersection then says
the common intersection of all P_C=M0;C is exactly M0.

Take ANY original-G-invariant quotient state R with a nonempty
ORIGINAL positive old-word profile, no intersection with M0,
and possibly QUOTIENT diagonal. All P_C have actual positive
original old-word profiles from C23, the old-G finite external
orbit family and the proved original SAP quotient semigroup.

If R met EVERY P_C, then the FINITE family consisting of R and all
P_C would have pairwise intersections: P_C all contain M0 by the
actual C40 reset, and R meets each P_C by assumption.
The proved original OLD positive STRONG 2-Helly from CCO+SAP supplies
one common quotient pair. OWL-I puts it in M0, contradicting R.

Therefore some ACTUAL complete external C has R ∩ (M0;C)=∅.
This is the source's finite escape step, including genuine diagonal
states, not a hypothesized escape oracle or the final layer theorem.

No quotient-reduct action/CCO/SAP, extra word assumption for K°,
or weakening of the source theorem.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- An actual positive original-G-invariant quotient state R,
nonempty and disjoint from the COMPLETE reset orbital M0, has a
genuine escape via SOME complete old-G external quotient orbital C,
as long as the source OWL contradiction assumption holds.

The output is a *specific real old K-external pair* c,d and literal
nonintersection of R with M0;C. No return/recurrence is assumed or
inferred here; those are the remaining finite-state argument.
-/
theorem original_positive_quotient_state_escape
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (J K : ColourEq S i)
    (hJK : J ≤ K) (hJ : (⊥ : ColourEq S i) < J)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J)
    (a b : X i) (hab : K a b) (hNotJab : ¬ J a b)
    (hReset : RawSymmetric.compose
      (originalQuotientOrbital S (G := G) J a b)
      (originalQuotientOrbital S (G := G) J a b) =
        (originalUpperSetoid S J K hJK).r)
    (hDifferent : ∃ c d : X i, K c d ∧ ¬ J c d ∧
      originalQuotientOrbital S (G := G) J c d ≠
        originalQuotientOrbital S (G := G) J a b)
    (hNoMixedFull : ∀ c d : X i, K c d → ¬ J c d →
      originalQuotientOrbital S (G := G) J c d ≠
        originalQuotientOrbital S (G := G) J a b →
      RawSymmetric.compose
        (originalQuotientOrbital S (G := G) J a b)
        (originalQuotientOrbital S (G := G) J c d) ≠
        originalQuotientExternalLayer S J K hJK)
    (R : OriginalInvariantQuotientState S H J)
    (hPositive : OriginalPositiveQuotientState S J R.val)
    (hNonempty : ∃ q r : Quotient J.val, R.val q r)
    (hDisjoint : ∀ q r : Quotient J.val,
      R.val q r →
        ¬ originalQuotientOrbital S (G := G) J a b q r) :
    ∃ c d : X i, K c d ∧ ¬ J c d ∧
      ¬ ∃ q r : Quotient J.val, R.val q r ∧
        RawSymmetric.compose
          (originalQuotientOrbital S (G := G) J a b)
          (originalQuotientOrbital S (G := G) J c d) q r := by
  classical
  let Ext := OriginalExternalQuotientState S H J K
  letI : Fintype Ext := Fintype.ofFinite Ext
  let n : Nat := Fintype.card Ext
  let e : Ext ≃ Fin n := Fintype.equivFin Ext
  let C : Fin n → Ext := e.symm
  let M : Quotient J.val → Quotient J.val → Prop :=
    originalQuotientOrbital S (G := G) J a b
  let P : Fin n → Quotient J.val → Quotient J.val → Prop :=
    fun j => RawSymmetric.compose M (C j).val.val
  let Mext : Ext :=
    originalExternalQuotientState_of_pair S H J K a b hab hNotJab
  have hMpositive : OriginalPositiveQuotientState S J M :=
    originalExternalQuotientState_positive
      S H sap J K hJ wJ hwJ Mext
  have hPpositive : ∀ j : Fin n,
      OriginalPositiveQuotientState S J (P j) := by
    intro j
    exact original_positive_quotient_state_comp
      S H sap J hJ M (C j).val.val hMpositive
      (originalExternalQuotientState_positive
        S H sap J K hJ wJ hwJ (C j))
  have hMsubset : ∀ j : Fin n, ∀ q r : Quotient J.val,
      M q r → P j q r := by
    intro j q r hM
    obtain ⟨c,d,hKcd,_,hEq⟩ := (C j).property
    have hSub :=
      original_reset_orbital_subset_comp_every_K_orbital
        S H J K hJK a b c d hKcd hReset q r hM
    change RawSymmetric.compose M (C j).val.val q r
    rw [hEq]
    exact hSub
  by_contra hNoEscape
  have hMeet : ∀ j : Fin n,
      ∃ q r : Quotient J.val, R.val q r ∧ P j q r := by
    intro j
    by_contra hNone
    apply hNoEscape
    obtain ⟨c,d,hKcd,hNotJcd,hEq⟩ := (C j).property
    refine ⟨c,d,hKcd,hNotJcd,?_⟩
    rintro ⟨q,r,hR,hMC⟩
    apply hNone
    refine ⟨q,r,hR,?_⟩
    change RawSymmetric.compose M (C j).val.val q r
    rw [hEq]
    exact hMC
  let states : Fin (n+1) →
      Quotient J.val → Quotient J.val → Prop :=
    Fin.cons R.val P
  let wordR : PositiveWord S i i := Classical.choose hPositive
  let words : Fin (n+1) → PositiveWord S i i :=
    Fin.cons wordR (fun j => Classical.choose (hPpositive j))
  have hWords : ∀ k : Fin (n+1),
      S.menuRel (PositiveWord.profile S (words k)) =
        quotientDiversity J.val (states k) := by
    intro k
    induction k using Fin.cases with
    | zero =>
        simpa only [words,states,Fin.cons_zero,wordR] using
          (Classical.choose_spec hPositive)
    | succ j =>
        simpa only [words,states,Fin.cons_succ] using
          (Classical.choose_spec (hPpositive j))
  have hPair : ∀ k l : Fin (n+1),
      ∃ q r : Quotient J.val, states k q r ∧ states l q r := by
    intro k l
    induction k using Fin.cases with
    | zero =>
        induction l using Fin.cases with
        | zero =>
            obtain ⟨q,r,hR⟩ := hNonempty
            exact ⟨q,r,hR,hR⟩
        | succ j =>
            simpa only [states,Fin.cons_zero,Fin.cons_succ] using hMeet j
    | succ j =>
        induction l using Fin.cases with
        | zero =>
            obtain ⟨q,r,hR,hP⟩ := hMeet j
            exact ⟨q,r,hP,hR⟩
        | succ k =>
            have hRoot : M (Quotient.mk J.val a)
                (Quotient.mk J.val b) :=
              originalQuotientOrbital_root S (G := G) J a b
            exact ⟨Quotient.mk J.val a,Quotient.mk J.val b,
              hMsubset j _ _ hRoot,hMsubset k _ _ hRoot⟩
  obtain ⟨q,r,hCommon⟩ :=
    original_positive_quotient_states_finite_helly
      S H sap cco J hJ states words hWords hPair
  have hRqr : R.val q r := by
    simpa only [states,Fin.cons_zero] using hCommon 0
  have hAll : ∀ c d : X i, K c d → ¬ J c d →
      RawSymmetric.compose M
        (originalQuotientOrbital S (G := G) J c d) q r := by
    intro c d hKcd hNotJcd
    let T : Ext :=
      originalExternalQuotientState_of_pair S H J K c d hKcd hNotJcd
    let j : Fin n := e T
    have hFrom : P j q r := by
      simpa only [states,Fin.cons_succ] using hCommon j.succ
    have hEq : C j = T := by
      dsimp [j,C]
      exact e.symm_apply_apply T
    change RawSymmetric.compose M (C j).val.val q r at hFrom
    rw [hEq] at hFrom
    exact hFrom
  have hMqr :=
    original_reset_external_intersection_subset_orbital
      S H J K hJK a b hab hDifferent hNoMixedFull q r hAll
  exact hDisjoint q r hRqr hMqr

end CCO.TerminalLattice
