import CCO.TerminalLattice.OriginalQuotientPeirce

/-!
# B050 source09 OWL-I: one intersection forces an entire external orbital

For the original non-index-two full cover, the finite escape argument
tests the relations P_C = M0 ; C, where M0 and C are COMPLETE pair
orbitals for the ORIGINAL ambient automorphism group on the quotient.

If the complete quotient pair orbital S meets P_C, Peirce rotation
yields an actual intersection of C with M0 ; S. Since M0 ; S is
invariant for the SAME original group, this one pair forces the ENTIRE
orbit C to be contained in M0 ; S.

Quantifying this statement over all external C gives the exact
external-layer coverage: whenever one complete orbit S meets every
P_C, its product with M0 contains ALL external quotient pairs. The
quotient diagonal is NOT inserted or deleted by this theorem.
No quotient-redacted automorphisms, quotient SAP/CCO or invented
positive relation assumptions.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- One genuine overlap of the COMPLETE original-G quotient orbital
S(x,y) with P_C=M0;C implies that the ENTIRE complete old-G
orbital C is contained in M0;S.

This is Peirce rotation, followed by real old-G orbit saturation;
it handles an arbitrary quotient pair q,r, even a diagonal pair,
rather than assuming S is disjoint from quotient equality. -/
theorem original_reset_Peirc_complete_orbital_cover
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i)
    (a b x y c d : X i)
    (q r : Quotient J.val)
    (hS : originalQuotientOrbital S (G := G) J x y q r)
    (hMC : RawSymmetric.compose
      (originalQuotientOrbital S (G := G) J a b)
      (originalQuotientOrbital S (G := G) J c d) q r) :
    ∀ u v : Quotient J.val,
      originalQuotientOrbital S (G := G) J c d u v →
        RawSymmetric.compose
          (originalQuotientOrbital S (G := G) J a b)
          (originalQuotientOrbital S (G := G) J x y) u v := by
  let M : Quotient J.val → Quotient J.val → Prop :=
    originalQuotientOrbital S (G := G) J a b
  let C : Quotient J.val → Quotient J.val → Prop :=
    originalQuotientOrbital S (G := G) J c d
  let T : Quotient J.val → Quotient J.val → Prop :=
    originalQuotientOrbital S (G := G) J x y
  have hSymm : ∀ q r, M q r → M r q :=
    originalQuotientOrbital_symmetric S H J a b
  obtain ⟨u,v,hMT,hC⟩ :=
    (original_peirce_intersection M C T hSymm).mp
      ⟨q,r,hMC,hS⟩
  let MState : OriginalInvariantQuotientState S H J :=
    ⟨M,originalQuotientOrbital_invariant S H J a b⟩
  let TState : OriginalInvariantQuotientState S H J :=
    ⟨T,originalQuotientOrbital_invariant S H J x y⟩
  let P := originalInvariantQuotientState_comp S H J MState TState
  have hMeet : ∃ u v : Quotient J.val,
      C u v ∧ P.val u v := ⟨u,v,hC,hMT⟩
  exact original_complete_quotient_orbital_subset_of_invariant_meeting
    S H J c d P hMeet

/-- The TRUE external K/J layer: an equivalence-related quotient pair
of DIFFERENT original J-classes. This is NOT K° on old real points;
the omitted equality is solely the quotient diagonal. -/
def originalQuotientExternalLayer
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K) :
    Quotient J.val → Quotient J.val → Prop :=
  fun q r => originalUpperSetoid S J K hJK q r ∧ q ≠ r

/-- SOURCE OWL-I core: if one COMPLETE original-G quotient orbital S
meets M0;C for every ACTUAL K-external complete orbital C, then
M0;S contains the WHOLE external K/J layer.

The proof selects actual old representatives of every quotient
external pair, uses full original K/J (not abstract quotient SAP)
to recognize the external old pair, and applies Peirce rotation
and the old-group complete-orbit saturation.

No assertion that M0;S avoids or contains quotient diagonal is made.
That separate issue is handled by the exact C45 two-return lemma.
-/
theorem original_reset_Peirc_covers_external_layer
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (a b x y : X i)
    (q r : Quotient J.val)
    (hS : originalQuotientOrbital S (G := G) J x y q r)
    (hAll : ∀ c d : X i, K c d → ¬ J c d →
      RawSymmetric.compose
        (originalQuotientOrbital S (G := G) J a b)
        (originalQuotientOrbital S (G := G) J c d) q r) :
    ∀ u v : Quotient J.val,
      originalQuotientExternalLayer S J K hJK u v →
        RawSymmetric.compose
          (originalQuotientOrbital S (G := G) J a b)
          (originalQuotientOrbital S (G := G) J x y) u v := by
  intro u v huv
  induction u using Quotient.inductionOn with
  | _ c =>
    induction v using Quotient.inductionOn with
    | _ d =>
      have hKcd : K c d :=
        (originalUpperSetoid_mk S J K hJK c d).mp huv.1
      have hNotJ : ¬ J c d := by
        intro hcd
        exact huv.2 (Quotient.sound hcd)
      exact original_reset_Peirc_complete_orbital_cover
        S H J a b x y c d q r hS
        (hAll c d hKcd hNotJ)
        (Quotient.mk J.val c) (Quotient.mk J.val d)
        (originalQuotientOrbital_root S (G := G) J c d)

end CCO.TerminalLattice
