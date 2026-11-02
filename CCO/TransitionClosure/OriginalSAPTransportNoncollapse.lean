import CCO.TransitionClosure.OriginalSAPFunctionalRigidity
import CCO.TerminalLattice.FibreSAP

/-!
# B049 C24-C30: actual ORIGINAL invariant RAW quotient transport no-collapse

The generic accepted B040 quotient transport takes an invariant
equality-inclusive RAW R:a→b and source invariant equivalence E with
R;Rᵒᵖ⊆E, producing its genuine canonical target kernel F.
This source consumer turns the ORIGINAL old colour-invariant J
into the SAME-group B040 invariant E, proves nontrivial original
J has a genuine pair of distinct old points, and obtains an ACTUAL
transport T from real original homogeneous transitivity and the
given RAW kernel premise.

Original old SAP then proves F has genuinely distinct related old
target points, including cross-sort R. No quotient SAP/CCO, full NR2,
represented exactness, real quotient section or new definability
premise enters the claim.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- The FULL original finite-colour invariant equivalence is also
invariant under precisely the ORIGINAL homogeneous ambient group.
The underlying setoid is not replaced by a quotient automorphism
group or an exact sublattice member. -/
def originalColourEqAsInvEq
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i) :
    QuotientTransport.InvEq G (X i) :=
  ⟨J.val,colourInvariant_groupInvariant S H J.property⟩

/-- Genuine B040 transport source instance: given the actual original
RAW typed relation R with true original G-invariance, nonemptiness,
and literal source-kernel bound R;Rᵒᵖ⊆J, the original transitive
homogeneous source supplies all generic transport witnesses.

For ORIGINAL nonzero J and old AgeSAP the resulting target kernel
F has a genuinely distinct OLD target pair; F is not equality.
This discharges the nonidentity gate before naming a proper
hidden quotient coordinate; it does not claim F is represented
RAW exact (the separate terminal FULL NR2 gate). -/
theorem original_source_transport_nonidentity_target
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (R : QuotientTransport.Rel (X i) (X j))
    (hInv : QuotientTransport.Invariant (G := G) R)
    (hNonempty : ∃ x : X i, ∃ y : X j, R x y)
    (hKernel : ∀ x x' : X i,
      QuotientTransport.compose R (QuotientTransport.converse R) x x' →
      J x x') :
    ∃ T : QuotientTransport.Transport
        (originalColourEqAsInvEq S H J) R,
      ∃ y z : X j, T.target y z ∧ y ≠ z := by
  let E := originalColourEqAsInvEq S H J
  let T : QuotientTransport.Transport E R :=
    QuotientTransport.typed_quotient_transport E R
      hInv hNonempty
      (S.original_sort_transitive_of_homogeneous H i)
      (S.original_sort_transitive_of_homogeneous H j)
      (fun x x' h => hKernel x x' h)
  have hNontrivial : ∃ x z : X i, E x z ∧ x ≠ z :=
    actual_nontrivial_equiv_pair S J hJ
  exact ⟨T,original_SAP_transport_preserves_nonidentity
    S H sap E hNontrivial R T⟩

end CCO.TransitionClosure
