import CCO.TransitionClosure.OriginalTransportComposition
import CCO.RealClosure.Bounds.TerminalNR2

/-!
# B049 source07 C25-C37: FULL original target quotient and terminal naming

Every FULL old colour-invariant equivalence is exactly an
equivalence invariant under the ORIGINAL homogeneous ambient
group G. The two descriptions are order-isomorphic, because
old pair homogeneity converts G-invariance back to literal
constancy on the original optional pair atom colours.

Consequently an actual accepted B040 transport T:E→F
has an ACTUAL FULL old target ColourEq F on the original
target sort. Its literal kernel is Rᵒᵖ;E;R, not a guessed
additional quotient. Original age SAP excludes equality
targets for E>Id and properness of E excludes F=Top;
those remain SEPARATE proved statements.

Only under the source's separate TERMINAL FULL NR2 input
does the accepted B011 old closure theorem construct
one actual equality-inclusive ORIGINAL RAW word for F.
No represented/exact sublattice is substituted for the
full invariant lattice; no quotient SAP/CCO, hidden
completion or artificial STRONG identity is inferred.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.QuotientTransport

/-- ACTUAL full equivalence lattice identification:
a colour-invariant original setoid and an invariant
setoid for the ORIGINAL homogeneous group G are precisely
the same full orbit-constant equivalences. The order
is the literal pointwise relation order, including
true old diagonal; no exact or represented restriction.
-/
def originalFullColourEqInvEqOrderIso
    (H : HomogeneousSource S G) {i : ι} :
    ColourEq S i ≃o InvEq G (X i) where
  toFun := originalColourEqAsInvEq S H
  invFun E := ⟨E.val, groupInvariant_colourInvariant S H E.property⟩
  left_inv J := by
    apply ColourEq.ext
    intro x y
    exact Iff.rfl
  right_inv E := by
    apply InvEq.ext
    intro x y
    exact Iff.rfl
  map_rel_iff' := by
    intro J K
    exact Iff.rfl

/-- The true source-named FULL invariant target
equivalence on the original sort j associated with
B040's canonical RAW quotient transition. -/
noncomputable def originalTransportTargetColourEq
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R) :
    ColourEq S j :=
  (originalFullColourEqInvEqOrderIso S H).symm T.target

/-- Exact original REAL typed B040 transported-kernel semantics:
F(y,z) iff some two original R-predecessors are J-related.
The equality-inclusive RAW relation, not a STRONG diversity
menu or an unrelated quotient kernel, is the target.
-/
theorem originalTransportTargetColourEq_iff
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (y z : X j) :
    originalTransportTargetColourEq S H J T y z ↔
      ∃ x x' : X i, R x y ∧ J x x' ∧ R x' z := by
  change T.target y z ↔ _
  exact T.target_iff y z

/-- The actual original homogeneous old-G source and original
age SAP make the FULL target equivalence a genuine
proper NONIDENTITY original quotient whenever J is
strictly between identity and Top.

The nonzero conclusion consumes visible OLD SAP; the
proper conclusion follows from the actual generic quotient
bijection and needs NO quotient SAP. Named RAW-exactness
is NOT asserted by these strict inequalities. -/
theorem originalTransportTargetColourEq_proper_nonzero
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (J : ColourEq S i)
    (hJbot : (⊥ : ColourEq S i) < J)
    (hJtop : J < (⊤ : ColourEq S i))
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R) :
    (⊥ : ColourEq S j) < originalTransportTargetColourEq S H J T ∧
      originalTransportTargetColourEq S H J T < (⊤ : ColourEq S j) := by
  let F : ColourEq S j := originalTransportTargetColourEq S H J T
  have hPair : ∃ y z : X j, F y z ∧ y ≠ z := by
    obtain ⟨y,z,hF,hne⟩ :=
      original_SAP_transport_preserves_nonidentity S H sap
        (originalColourEqAsInvEq S H J)
        (CCO.TerminalLattice.actual_nontrivial_equiv_pair S J hJbot) R T
    exact ⟨y,z,hF,hne⟩
  have hNotBot : F ≠ ⊥ := by
    intro hEq
    obtain ⟨y,z,hF,hne⟩ := hPair
    rw [hEq] at hF
    exact hne hF
  have hProperT : T.target ≠ ⊤ :=
    original_transport_target_proper T
      (original_colourEq_proper_as_invariant S H J (ne_of_lt hJtop))
  have hNotTop : F ≠ ⊤ := by
    intro hEq
    apply hProperT
    apply InvEq.ext
    intro y z
    constructor
    · intro _
      exact (InvEq.top_apply y z).mpr trivial
    · intro _
      have hF : F y z := by
        rw [hEq]
        exact (ColourEq.top_apply S j y z).mpr trivial
      exact hF
  constructor
  · exact lt_of_le_of_ne bot_le hNotBot.symm
  · exact lt_of_le_of_ne le_top hNotTop

/-- SOURCE07 separate C37 terminal represented-membership gate:
under the source's ACTUAL full original no-index-two condition
(B011, not a new assumption on F itself), EVERY original
FULL transported invariant kernel F has one genuine
equality-inclusive ORIGINAL RAW atomic word. This is
not a claim of a positive STRONG word or a hidden age SAP.
-/
theorem originalTransportTargetColourEq_raw_word_of_NR2
    (H : HomogeneousSource S G)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R) :
    ∃ word : RawWord S j j,
      RawWord.relation S word =
        (originalTransportTargetColourEq S H J T).val.r :=
  RealClosure.Bounds.terminal_raw_word_of_originalNR2 S H nr2
    (originalTransportTargetColourEq S H J T)

end CCO.TransitionClosure
