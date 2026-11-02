import CCO.TransitionClosure.OriginalTransitionGraphSpectrum

/-!
# B049 source07 C46-C52: WHOLE literal invariant RAW transport cylinder

This closes the important distinction between the actual full invariant
R (a union of original fine orbitals, possibly including equality) and
one particular fine old diversity atom a⊆R.

For the REAL B040 canonical transport, the literal equality-inclusive
(J;R;K) relation is exactly the pullback of the graph of its quotient
bijection, with K=Rᵒᵖ;J;R the actual FULL original target equivalence.
The old atomic quotient graph theorem proves the SAME relation with
the single old atom a. Thus their actual RAW sandwiches, including
possible logical identity at the endpoints, coincide. Taking genuine
diversity guards yields exactly the source's full OLD graph spectrum.
Under terminal FULL original NR2 this is an actually positive typed
old STRONG word, with NO claim that R itself is an atomic word.

There is no hidden/quotient SAP/CCO or quotient-reduct automorphism group.
The finite named hidden coordinate language remains a separate consumer.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.QuotientTransport
open CCO.TerminalLattice

/-- The actual equality-inclusive typed old RAW J;R;K sandwich,
with two exterior FULL original equivalences and a literal middle
invariant relation. It does not delete equality or add a STRONG unit. -/
def originalRawFullTypedSandwich {i j : ι}
    (J : ColourEq S i) (K : ColourEq S j)
    (R : QuotientTransport.Rel (X i) (X j)) :
    X i → X j → Prop :=
  fun x y => ∃ u : X i, ∃ v : X j,
    J x u ∧ R u v ∧ K v y

/-- Exact B040 graph characterisation for the WHOLE relation R.
A real x,y lies in actual old RAW J;R;K iff its quotient classes
are related by the real canonical quotient bijection q_(R,J).
No atom selection, positive word, SAP, terminality or hidden
quotient action is required here. -/
theorem original_raw_full_transport_sandwich_iff_graph
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (x : X i) (y : X j) :
    originalRawFullTypedSandwich S J
        (originalTransportTargetColourEq S H J T) R x y ↔
      T.quotientEquiv (Quotient.mk J.val x) =
        (Quotient.mk
          (originalTransportTargetColourEq S H J T).val y) := by
  let K : ColourEq S j := originalTransportTargetColourEq S H J T
  constructor
  · rintro ⟨u,v,hJu,hRuv,hKvy⟩
    have hq : (Quotient.mk J.val x) = Quotient.mk J.val u :=
      Quotient.sound hJu
    have hr : (Quotient.mk K.val v) = Quotient.mk K.val y :=
      Quotient.sound hKvy
    have hEdge :
        T.quotientEquiv (Quotient.mk J.val u) =
          (Quotient.mk K.val v) :=
      T.quotientEquiv_edge hRuv
    exact (congrArg T.quotientEquiv hq).trans (hEdge.trans hr)
  · intro hxy
    obtain ⟨v,hRv⟩ := T.serial x
    have hEdge :
        T.quotientEquiv (Quotient.mk J.val x) = Quotient.mk K.val v :=
      T.quotientEquiv_edge hRv
    have hKvy : K v y :=
      Quotient.exact (hEdge.symm.trans hxy)
    exact ⟨x,v,J.val.refl x,hRv,hKvy⟩

/-- The full equality-inclusive OLD RAW J;R;K sandwich equals
J;{a};K for EVERY genuine old fine atom a in the diversity of
the original invariant RAW relation R, provided R;Rᵒᵖ≤J.

The nontrivial direction uses a real graph pair and the proved
pointwise atomic quotient test; the reverse direction embeds
the entire old fine a-orbital in R via original homogeneity.
This is equality of saturated RAW relations, NOT equality R=a. -/
theorem original_raw_full_transport_sandwich_eq_atom
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (a : S.Atom i j) (ha : a ∈ S.diversityGuard R) :
    originalRawFullTypedSandwich S J
        (originalTransportTargetColourEq S H J T) R =
      originalRawTypedSandwich S J
        (originalTransportTargetColourEq S H J T) a := by
  let K : ColourEq S j := originalTransportTargetColourEq S H J T
  have hInside : ∀ x : X i, ∀ y : X j,
      S.atomRel a x y → R x y :=
    original_invariant_raw_contains_full_atom
      S H R T.invariant a ha
  funext x y
  apply propext
  constructor
  · intro hRaw
    have hGraph :
        T.quotientEquiv (Quotient.mk J.val x) =
          (Quotient.mk K.val y) :=
      (original_raw_full_transport_sandwich_iff_graph S H J T x y).mp hRaw
    have hAtom :
        a ∈ originalTypedQuotientPairSpectrum S J K
          (Quotient.mk J.val x) (Quotient.mk K.val y) :=
      (original_transport_graph_iff_atom_in_pair_spectrum
        S H J T a ha (Quotient.mk J.val x) (Quotient.mk K.val y)).mp hGraph
    obtain ⟨u,v,hqu,hrv,hAUv⟩ := hAtom
    exact ⟨u,v,J.val.symm (Quotient.exact hqu),hAUv,Quotient.exact hrv⟩
  · rintro ⟨u,v,hJu,hAUv,hKvy⟩
    exact ⟨u,v,hJu,hInside u v hAUv,hKvy⟩

/-- SOURCE07 QT-Graph, WHOLE-R RAW diversity form:
the representative graph spectrum is the entire true OLD
diversity guard of J;R;K and equals that of J;{a};K.
No hidden type partition, positivity or invented identity is
assumed merely to establish this exact equality. -/
theorem original_raw_full_transport_guard_eq_atomic
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (a : S.Atom i j) (ha : a ∈ S.diversityGuard R) :
    S.diversityGuard (originalRawFullTypedSandwich S J
      (originalTransportTargetColourEq S H J T) R) =
      S.diversityGuard (originalRawTypedSandwich S J
        (originalTransportTargetColourEq S H J T) a) := by
  exact congrArg (fun W : X i → X j → Prop => S.diversityGuard W)
    (original_raw_full_transport_sandwich_eq_atom S H J T a ha)

/-- For every actually matched quotient pair, the FULL invariant
R-graph REAL representative diversity spectrum is one genuinely
positive OLD typed word at terminal original FULL NR2 (and source
nonzero proper J). The representing word is concretely J°;a;K°,
NOT an unsupported positive word for the union R itself.

This is the precise equality-inclusive RAW whole-branch bridge
needed before the separate named hidden-coordinate and full
semantic-cylinder binary-language consumer. -/
theorem original_terminal_full_transport_graph_positive_word
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
        S.diversityGuard (originalRawFullTypedSandwich S J
          (originalTransportTargetColourEq S H J T) R) := by
  obtain ⟨p,hp⟩ :=
    original_terminal_matched_transition_graph_positive_word
      S H sap nr2 J hJbot hJtop T a ha q r hqr
  refine ⟨p,?_⟩
  calc
    PositiveWord.profile S p =
        originalTypedQuotientPairSpectrum S J
          (originalTransportTargetColourEq S H J T) q r := hp
    _ = S.diversityGuard (originalRawTypedSandwich S J
          (originalTransportTargetColourEq S H J T) a) :=
      original_transport_matched_pair_spectrum_eq_raw
        S H J T a ha q r hqr
    _ = S.diversityGuard (originalRawFullTypedSandwich S J
          (originalTransportTargetColourEq S H J T) R) :=
      (original_raw_full_transport_guard_eq_atomic S H J T a ha).symm

end CCO.TransitionClosure
