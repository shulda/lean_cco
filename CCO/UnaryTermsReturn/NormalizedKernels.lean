import CCO.UnaryTermsReturn.NamedIntermediate
import CCO.TransitionClosure.OriginalUnaryTermNormalization
import CCO.TransitionClosure.OriginalFullMITransport

/-!
# B052 C02/C03/C22–C24 — actual named normal-source kernels

B049 normalizes arbitrary original hidden unary expressions to one
actual source upward E<=J followed by one genuine RAW transition R.
An intermediate FULL J in a *generic* raw normal form is not
automatically a represented proper MI. For a genuine named term
whose final kernel is a represented proper MI F, the FULL B040
upper-interval transport isomorphism proves that the intermediate
J is also proper MI (not just meet-irreducible in a restricted
already-named sublattice). The source original FULL NR2 then gives
an ACTUAL RAW name for J, and the literal source inequality E<=J
ensures J>Id.

The original finite word / edge interpretation is retained. No new
SAP, CCO, hidden-age hypothesis, quotient chart, axiom or stronger
named-kernel premise is added. The subsequent identification of
the remaining RAW transition with a specific named symbol or
existing identity is a separate normal-form task.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original
open CCO.QuotientTransport

/-- B052 transport closure on the WHOLE invariant lattice, not
only a selected represented subfamily. If the *actual* target of
a finite normal RAW datum is proper meet-irreducible, its literal
intermediate source kernel is proper meet-irreducible too.
This is the inverse direction of B040's genuine interval isomorphism:
the target is the ACTUAL Rᵒᵖ;J;R kernel. -/
theorem original_normal_middle_properMI
    (H : HomogeneousSource S G)
    {i j : ι} (N : OriginalCanonicalUnaryNormalDatum S (G := G) i j)
    (hTargetMI : ProperMeetIrreducible
      (originalColourEqAsInvEq S H
        (originalTransportTargetColourEq S H N.val.2.val.1
          (originalCanonicalRawTransitionDatum_transport S H N.val.2)))) :
    ProperMeetIrreducible
      (originalColourEqAsInvEq S H N.val.2.val.1) := by
  let J : ColourEq S i := N.val.2.val.1
  let T := originalCanonicalRawTransitionDatum_transport S H N.val.2
  have hTarget : ProperMeetIrreducible T.target := by
    have hIso :=
      (originalFullColourEqInvEqOrderIso S H
        (i := j)).apply_symm_apply T.target
    rw [← hIso]
    exact hTargetMI
  have hPush :
      T.push (originalColourEqAsInvEq S H J) le_rfl = T.target := by
    apply InvEq.ext
    intro y z
    exact (T.push_iff _ le_rfl y z).trans (T.target_iff y z).symm
  apply (T.push_meetIrreducible
      (originalColourEqAsInvEq S H J) le_rfl).mp
  rwa [hPush]

/-- The actual FULL normal kernel J is an EXISTING named hidden
coordinate if the source is a genuinely nonidentity represented
coordinate and the terminal FULL NR2 condition is supplied.
An original source E<=J makes J nonzero; the target proper MI
hypothesis pulls back through the true B040 transport. -/
theorem original_normal_middle_named
    (H : HomogeneousSource S G)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (N : OriginalCanonicalUnaryNormalDatum S (G := G) i j)
    (hSource : (⊥ : ColourEq S i) < N.val.1)
    (hTargetMI : ProperMeetIrreducible
      (originalColourEqAsInvEq S H
        (originalTransportTargetColourEq S H N.val.2.val.1
          (originalCanonicalRawTransitionDatum_transport S H N.val.2)))) :
    ∃ K : OriginalNamedHiddenCoordinate S H i,
      K.val = N.val.2.val.1 ∧ N.val.1 ≤ K.val := by
  have hNonzero : (⊥ : ColourEq S i) < N.val.2.val.1 :=
    lt_of_lt_of_le hSource N.property
  let K : OriginalNamedHiddenCoordinate S H i :=
    original_full_MI_named_hidden_of_terminalNR2 S H nr2
      N.val.2.val.1 hNonzero
        (original_normal_middle_properMI S H N hTargetMI)
  exact ⟨K, rfl, N.property⟩

/-- A whole ACTUAL named hidden unary word, of UNBOUNDED length,
normalizes over an actual *named* intermediate proper FULL MI K.
Its original kernel E<=K, literal old RAW transition R and its
target F are the real ones; the edge semantics hold pointwise.

This supplies the named-kernel gate of source10 QT-NF without
assuming that the generic B049 finite normal-data source K was
already named. The remaining final term-symbol/identity selection
is treated separately. -/
theorem original_named_hidden_term_has_named_normal_middle
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι}
    (D : OriginalNamedHiddenCoordinate S H i)
    (F : OriginalNamedHiddenCoordinate S H j)
    (word : OriginalNamedRawUnaryTerm S H sap nr2 D F) :
    ∃ N : OriginalCanonicalUnaryNormalDatum S (G := G) i j,
      N.val.1 = D.val ∧
      originalTransportTargetColourEq S H N.val.2.val.1
          (originalCanonicalRawTransitionDatum_transport S H N.val.2) = F.val ∧
      (∃ K : OriginalNamedHiddenCoordinate S H i,
        K.val = N.val.2.val.1 ∧ D.val ≤ K.val) ∧
      (∀ (x : X i) (y : X j),
        N.val.2.val.2.val.val x y →
          OriginalNamedRawUnaryTerm.eval S H sap nr2 word
            (Quotient.mk D.val.val x) = Quotient.mk F.val.val y) := by
  obtain ⟨N, hSource, hTarget, hEdge⟩ :=
    OriginalOldUnaryWord.normal_relation S H
      (OriginalNamedRawUnaryTerm.toOld S H sap nr2 word)
  have hTargetMI : ProperMeetIrreducible
      (originalColourEqAsInvEq S H
        (originalTransportTargetColourEq S H N.val.2.val.1
          (originalCanonicalRawTransitionDatum_transport S H N.val.2))) := by
    rw [hTarget]
    exact F.property.2.1
  have hSourceNonzero : (⊥ : ColourEq S i) < N.val.1 := by
    rw [hSource]
    exact D.property.1
  obtain ⟨K, hKernel, hDK⟩ :=
    original_normal_middle_named S H nr2 N
      hSourceNonzero hTargetMI
  refine ⟨N, hSource, hTarget, ⟨K, hKernel, ?_⟩, ?_⟩
  · exact hSource.symm ▸ hDK
  · intro x y hRel
    exact hEdge x y hRel

end CCO.UnaryTermsReturn
