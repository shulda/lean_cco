import CCO.TerminalLattice.OriginalQuotientOWLPathProduct

/-!
# B050 source09 OWL: the complete finite positive escape contradicts no mixed cover

This is the source's finite-state contradiction, not a substituted
conditional escape/periodicity provider. Start with a REAL complete
external original-G orbit different from the C40 reset orbit M0.
The proved old CCO+SAP positive-state 2-Helly yields an external
old-G orbit C for EACH positive state R avoiding M0, so that the
actual quotient composition R;C again avoids M0. Original SAP
supplies the positive old word of the entire new state. These
states form a finite type even if the quotient carrier is infinite.

Classical choice defines ONE genuine deterministic transition on
this proven finite type. Finite pigeonhole gives an actual
periodic R; its labelled circuit yields a NONEMPTY finite product
W of COMPLETE external original-G quotient orbitals with R;W=R.
The product is invariant, serial, inside K/J and has a REAL
off-diagonal quotient pair by the proved full-cover no-return.
Its eventual full powers force R=K/J, contradicting avoidance
of the actual reset orbital M0. No quotient diagonal is discarded.

The only contradicted hypothesis is the source's assumption that
NO distinct mixed complete external product M0;C covers the
external K/J layer. The genuine initial different orbital is an
explicit case condition; the singleton case is proved separately.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- SOURCE OWL finite escape contradiction, with ACTUAL source
hypotheses and exactly the temporary no-mixed-full case assumption.
Unlike the final OWL theorem this intermediate lemma explicitly
assumes a second distinct complete external orbital. All other
components, including the FINITE state type, every positive
successor, its periodic label product and its eventual full powers,
are internally PROVED rather than assumed.

In particular a periodically repeated state MAY contain quotient
diagonal pairs; no index-two or old equality shortcut is hidden.
-/
theorem original_no_mixed_full_impossible_of_different
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (J K : ColourEq S i)
    (hJK : J ⋖ K) (hJ : (⊥ : ColourEq S i) < J)
    (anchor : X i)
    (hNotTwo : relativeIndex J.val K.val anchor ≠ 2)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J)
    (a b : X i) (hab : K a b) (hNotJab : ¬ J a b)
    (hReset : RawSymmetric.compose
      (originalQuotientOrbital S (G := G) J a b)
      (originalQuotientOrbital S (G := G) J a b) =
        (originalUpperSetoid S J K hJK.le).r)
    (hDifferent : ∃ c d : X i, K c d ∧ ¬ J c d ∧
      originalQuotientOrbital S (G := G) J c d ≠
        originalQuotientOrbital S (G := G) J a b)
    (hNoMixedFull : ∀ c d : X i, K c d → ¬ J c d →
      originalQuotientOrbital S (G := G) J c d ≠
        originalQuotientOrbital S (G := G) J a b →
      RawSymmetric.compose
        (originalQuotientOrbital S (G := G) J a b)
        (originalQuotientOrbital S (G := G) J c d) ≠
        originalQuotientExternalLayer S J K hJK.le) :
    False := by
  classical
  let E := OriginalOWLEscapeState S H J K hJK.le a b
  let Ext := OriginalExternalQuotientState S H J K
  letI : Finite E :=
    originalOWLEscapeState_finite S H J K hJK.le a b
  have hSucc (R : E) : ∃ C : Ext, ∃ T : E,
      T.val.val = RawSymmetric.compose R.val.val C.val.val :=
    originalOWLEscapeState_successor
      S H sap cco J K hJK.le hJ wJ hwJ
        a b hab hNotJab hReset hDifferent hNoMixedFull R
  let label : E → Ext := fun R => Classical.choose (hSucc R)
  let next : E → E :=
    fun R => Classical.choose (Classical.choose_spec (hSucc R))
  have hNext (R : E) :
      (next R).val.val =
        RawSymmetric.compose R.val.val (label R).val.val :=
    Classical.choose_spec (Classical.choose_spec (hSucc R))
  let stateRel : E → Quotient J.val → Quotient J.val → Prop :=
    fun R => R.val.val
  let labelRel : E → Quotient J.val → Quotient J.val → Prop :=
    fun R => (label R).val.val
  have hOne (R : E) :
      stateRel (next R) =
        RawSymmetric.compose (stateRel R) (labelRel R) :=
    hNext R
  obtain ⟨c,d,hKcd,hNotJcd,hDifferentCd⟩ := hDifferent
  let start : E :=
    originalOWLEscapeState_initial
      S H sap J K hJK.le hJ wJ hwJ
      a b c d hKcd hNotJcd hDifferentCd
  obtain ⟨k,n,hPeriod⟩ :=
    original_finite_labelled_periodic_relation
      next labelRel stateRel hOne start
  let R : E := next^[k] start
  let W : OriginalInvariantQuotientState S H J :=
    original_OWL_external_path_state S H J K next label R n
  have hWValue : W.val =
      original_finite_labelled_product
        next labelRel R n :=
    original_OWL_external_path_state_val
      S H J K next label R n
  have hFixed : R.val.val =
      RawSymmetric.compose R.val.val W.val := by
    change R.val.val =
      RawSymmetric.compose R.val.val
        (original_finite_labelled_product
          next labelRel R n) at hPeriod
    rw [← hWValue] at hPeriod
    exact hPeriod
  have hWInside : ∀ q r : Quotient J.val,
      W.val q r → originalUpperSetoid S J K hJK.le q r :=
    original_OWL_external_path_state_inside_upper
      S H J K hJK.le next label R n
  have hWOff : ∃ q r : Quotient J.val,
      q ≠ r ∧ W.val q r :=
    original_OWL_external_path_state_offdiagonal
      S H J K hJK anchor hNotTwo next label R n
  have hAllUpper :=
    original_periodic_quotient_state_covers_upper
      S H J K hJK anchor hNotTwo R.val W
        R.property.2.1 R.property.2.2.1
        hWInside hWOff hFixed
  have hUpperRoot :
      originalUpperSetoid S J K hJK.le
        (Quotient.mk J.val a) (Quotient.mk J.val b) :=
    (originalUpperSetoid_mk S J K hJK.le a b).mpr hab
  have hMroot :
      originalQuotientOrbital S (G := G) J a b
        (Quotient.mk J.val a) (Quotient.mk J.val b) :=
    originalQuotientOrbital_root S (G := G) J a b
  exact R.property.2.2.2
    (Quotient.mk J.val a) (Quotient.mk J.val b)
      (hAllUpper _ _ hUpperRoot) hMroot

end CCO.TerminalLattice
