import CCO.TransitionClosure.OriginalAtomicTransport
import CCO.TransitionClosure.OriginalTerminalRepresentedWrappers
import CCO.TransitionClosure.OriginalTransportTargetFull

/-!
# B049 source07 C44-C52: actual quotient-transition graph cylinders

A genuine B040 transport T has the literal original target FULL kernel
K = Rᵒᵖ;J;R. For EVERY old fine atom a in its RAW R-diversity, the
already constructed actual atomic subtransport is serial on original
real representatives. Therefore a matched J/K-quotient pair contains
a real a-edge, and conversely any such a-edge certifies the exact
original canonical quotient transition function. This establishes
the source's WHOLE graph semantics without an invented quotient section
or an assumed hidden SAP.

Actual old two-point homogeneity then identifies the entire full OLD
representative spectrum of EVERY matched quotient pair with the
J;{a};K RAW diversity cylinder. When J,K are both original nonzero
and terminal original FULL NR2 is available, the old SAP saturation
identity and B011 positive RAW normalization construct ONE genuine
positive original typed word describing the whole graph spectrum.

None of these conclusions equates a fine atom a with the whole RAW
relation R, assumes an arbitrary quotient SAP/CCO, or treats quotient
equality as an old positive STRONG atom. A separate named-hidden-type
language and final complete B049 consumer remain to be constructed.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.QuotientTransport
open CCO.TerminalLattice

/-- Pointwise SOURCE07 QT-Graph, with the literal FULL old target
kernel K. A quotient class pair is matched by the REAL B040
canonical transition iff it admits a representative edge of ANY
chosen fine atom a contained in the original invariant RAW relation.

The forward direction uses the ACTUAL coserial/serial old atomic
transport, not any quotient SAP; the reverse direction uses the
proved a⊆R and the actual B040 quotient-equivalence edge law.
All original types and the same original group action are preserved. -/
theorem original_transport_graph_iff_atom_in_pair_spectrum
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (a : S.Atom i j) (ha : a ∈ S.diversityGuard R)
    (q : Quotient J.val)
    (r : Quotient (originalTransportTargetColourEq S H J T).val) :
    T.quotientEquiv q = r ↔
      a ∈ originalTypedQuotientPairSpectrum S J
        (originalTransportTargetColourEq S H J T) q r := by
  let K : ColourEq S j := originalTransportTargetColourEq S H J T
  have hInside : ∀ x : X i, ∀ y : X j,
      S.atomRel a x y → R x y :=
    original_invariant_raw_contains_full_atom
      S H R T.invariant a ha
  obtain ⟨Ta,_,_⟩ :=
    original_atomic_transport_agrees_with_whole_raw
      S H J R T a ha
  constructor
  · intro hqr
    induction q using Quotient.inductionOn with
    | _ x =>
        obtain ⟨y,hay⟩ := Ta.serial x
        have hTxy :
            T.quotientEquiv (Quotient.mk'' x) =
              (Quotient.mk'' y : Quotient T.target.val) :=
          T.quotientEquiv_edge (hInside x y hay)
        have hr : (Quotient.mk K.val y) = r :=
          hTxy.symm.trans hqr
        exact ⟨x,y,rfl,hr,hay⟩
  · rintro ⟨x,y,hqx,hry,hxy⟩
    calc
      T.quotientEquiv q =
          T.quotientEquiv (Quotient.mk'' x) := by rw [hqx]
      _ = Quotient.mk'' y := T.quotientEquiv_edge (hInside x y hxy)
      _ = r := hry

/-- Every matched true original quotient-transition graph pair has
the complete old diversity spectrum (J;{a};K)°, independent of its
chosen real representative, not merely the single fine type a.

This uses the proven full OLD representative-cylinder realization,
after the exact graph test above. No hidden quotient homogeneity,
additional represented equality or arbitrary real sort identification. -/
theorem original_transport_matched_pair_spectrum_eq_raw
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (a : S.Atom i j) (ha : a ∈ S.diversityGuard R)
    (q : Quotient J.val)
    (r : Quotient (originalTransportTargetColourEq S H J T).val)
    (hqr : T.quotientEquiv q = r) :
    originalTypedQuotientPairSpectrum S J
        (originalTransportTargetColourEq S H J T) q r =
      S.diversityGuard
        (originalRawTypedSandwich S J
          (originalTransportTargetColourEq S H J T) a) := by
  let K : ColourEq S j := originalTransportTargetColourEq S H J T
  obtain ⟨x,y,hqx,hry,hxy⟩ :=
    (original_transport_graph_iff_atom_in_pair_spectrum
      S H J T a ha q r).mp hqr
  calc
    originalTypedQuotientPairSpectrum S J K q r =
        originalTypedQuotientPairSpectrum S J K
          (Quotient.mk J.val x) (Quotient.mk K.val y) := by rw [hqx,hry]
    _ = S.diversityGuard (originalRawTypedSandwich S J K a) :=
      originalTypedQuotientPairSpectrum_eq_raw S H J K a x y hxy

/-- Source07 C48-C52 TRUE terminal positive graph presentation.
For a source nonzero proper FULL J, old visible SAP prevents the
literal transport target K from collapsing to equality. Terminal
FULL original NR2 independently provides positive old STRONG words
for both J° and K°. Concatenate those with the SINGLE chosen
genuine diversity atom a, obtaining exactly the full old spectrum
of EVERY matched original quotient graph pair.

This requires neither quotient SAP/CCO nor original CCO, and
the target remains the true transported FULL old equivalence,
not a hypothesized represented/hidden chart. -/
theorem original_terminal_matched_transition_graph_positive_word
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (J : ColourEq S i)
    (hJbot : (⊥ : ColourEq S i) < J)
    (hJtop : J < (⊤ : ColourEq S i))
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (a : S.Atom i j) (ha : a ∈ S.diversityGuard R)
    (q : Quotient J.val)
    (r : Quotient (originalTransportTargetColourEq S H J T).val)
    (hqr : T.quotientEquiv q = r) :
    ∃ p : PositiveWord S i j,
      PositiveWord.profile S p =
        originalTypedQuotientPairSpectrum S J
          (originalTransportTargetColourEq S H J T) q r := by
  let K : ColourEq S j := originalTransportTargetColourEq S H J T
  have hKbot : (⊥ : ColourEq S j) < K :=
    (originalTransportTargetColourEq_proper_nonzero
      S H sap J hJbot hJtop T).1
  obtain ⟨wJ,hwJ⟩ :=
    original_nonzero_equiv_positive_word_of_terminalNR2
      S H sap nr2 J hJbot
  obtain ⟨wK,hwK⟩ :=
    original_nonzero_equiv_positive_word_of_terminalNR2
      S H sap nr2 K hKbot
  let p : PositiveWord S i j :=
    PositiveWord.append S wJ
      (PositiveWord.append S (.single a) wK)
  refine ⟨p, ?_⟩
  calc
    PositiveWord.profile S p =
        S.product (PositiveWord.profile S wJ)
          (PositiveWord.profile S
            (PositiveWord.append S (.single a) wK)) :=
      PositiveWord.profile_append_of_SAP S H sap wJ
        (PositiveWord.append S (.single a) wK)
    _ = S.product (originalEquivDiversityPalette S J)
          (S.product ({a} : S.Menu i j)
            (originalEquivDiversityPalette S K)) := by
        rw [PositiveWord.profile_append_of_SAP S H sap (.single a) wK,
          hwJ,hwK]
        rfl
    _ = S.diversityGuard (originalRawTypedSandwich S J K a) :=
      (original_raw_typed_J_atom_K_guard_eq_strong
        S H sap J K hJbot hKbot a).symm
    _ = originalTypedQuotientPairSpectrum S J K q r :=
      (original_transport_matched_pair_spectrum_eq_raw
        S H J T a ha q r hqr).symm

end CCO.TransitionClosure
