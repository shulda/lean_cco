import CCO.TerminalLattice.OriginalQuotientPeirceCover
import CCO.TerminalLattice.OriginalQuotientOrbitalReturn

/-!
# B050 source09 OWL-I: the exact external-orbital intersection is M0

Under the contradiction hypothesis that no mixed product M0;C of
DISTINCT full external old-G quotient orbitals equals the entire
external layer Ubar=(K/J)\\Delta, the source's Peirce argument
identifies the intersection over ALL actual external COMPLETE
orbitals C of P_C=M0;C as precisely M0.

The source uses no artificial finite quotient carrier. The group is
the full ORIGINAL ambient G on J classes. The true quotient diagonal
is eliminated using the proved complete-orbital two-return test,
not by assuming a state is off-diagonal. Membership in an arbitrary
complete old-G orbit is propagated using actual G-invariance.

The no-full-mixed-product hypothesis is the actual contradiction
assumption for source OWL, NOT a premise of the ultimate layer theorem.
Its discharge is the remaining finite escape/Helly step.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- The complete original-G quotient pair orbital of any REAL old
K-pair is contained in the true upper K/J equivalence. This follows
from old K-invariance under G, not from homogeneity of a reduct.
-/
theorem originalQuotientOrbital_inside_originalUpper
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (a b : X i) (hab : K a b) :
    ∀ q r : Quotient J.val,
      originalQuotientOrbital S (G := G) J a b q r →
        originalUpperSetoid S J K hJK q r := by
  intro q r
  rintro ⟨g,hgq,hgr⟩
  have hKmove : K (g • a) (g • b) :=
    colourInvariant_groupInvariant S H K.2 g a b hab
  have hUpper :=
    (originalUpperSetoid_mk S J K hJK (g • a) (g • b)).mpr hKmove
  rw [hgq,hgr] at hUpper
  exact hUpper

/-- Composition of two complete real old-G quotient K-orbitals
stays inside the true K/J equivalence. Both factors may include
the quotient diagonal, although the external application excludes
it only later with the complete-orbital two-return test. -/
theorem originalTwoQuotientOrbitals_comp_inside_upper
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (a b c d : X i) (hab : K a b) (hcd : K c d) :
    ∀ q r : Quotient J.val,
      RawSymmetric.compose
        (originalQuotientOrbital S (G := G) J a b)
        (originalQuotientOrbital S (G := G) J c d) q r →
      originalUpperSetoid S J K hJK q r := by
  intro q r
  rintro ⟨mid,hM,hC⟩
  exact (originalUpperSetoid S J K hJK).trans
    (originalQuotientOrbital_inside_originalUpper
      S H J K hJK a b hab q mid hM)
    (originalQuotientOrbital_inside_originalUpper
      S H J K hJK c d hcd mid r hC)

/-- Exact SOURCE OWL-I difficult direction.

Suppose M0 is one COMPLETE original-G K-external orbit, there exists
a DIFFERENT K-external complete orbit, and (for contradiction)
NO mixed M0;C with C distinct from M0 equals the full external
layer. If (q,r) belongs to M0;C for EVERY actual K-external pair
orbit C, then (q,r) belongs to M0.

The proof first uses one other C to establish q K/J r and rule out
q=r by genuine two-orbit returns. Thus (q,r) is itself in an
actual external complete orbit S. If S differs from M0, the prior
Peirce rotation says M0;S contains ALL external K/J pairs. Its
upper containment and disjointness from the true quotient diagonal
force M0;S=Ubar, contradicting the no-mixed-full assumption.
-/
theorem original_reset_external_intersection_subset_orbital
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (a b : X i) (hab : K a b)
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
    (q r : Quotient J.val)
    (hAll : ∀ c d : X i, K c d → ¬ J c d →
      RawSymmetric.compose
        (originalQuotientOrbital S (G := G) J a b)
        (originalQuotientOrbital S (G := G) J c d) q r) :
    originalQuotientOrbital S (G := G) J a b q r := by
  obtain ⟨c,d,hKcd,hNotJcd,hDifferentCd⟩ := hDifferent
  have hPair := hAll c d hKcd hNotJcd
  have hUpper : originalUpperSetoid S J K hJK q r :=
    originalTwoQuotientOrbitals_comp_inside_upper
      S H J K hJK a b c d hab hKcd q r hPair
  have hOff : q ≠ r := by
    intro hEq
    subst r
    obtain ⟨mid,hM,hD⟩ := hPair
    have hCoincide :=
      (originalQuotientOrbital_two_return_iff_eq
        S H J a b c d).mp ⟨q,mid,hM,hD⟩
    exact hDifferentCd hCoincide.symm
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      have hKxy : K x y :=
        (originalUpperSetoid_mk S J K hJK x y).mp hUpper
      have hNotJxy : ¬ J x y := by
        intro hxy
        exact hOff (Quotient.sound hxy)
      let T : Quotient J.val → Quotient J.val → Prop :=
        originalQuotientOrbital S (G := G) J x y
      by_cases hTeq :
          T = originalQuotientOrbital S (G := G) J a b
      · have hRoot : T (Quotient.mk J.val x) (Quotient.mk J.val y) :=
          originalQuotientOrbital_root S (G := G) J x y
        rw [hTeq] at hRoot
        exact hRoot
      · have hContained :
            ∀ u v : Quotient J.val,
              originalQuotientExternalLayer S J K hJK u v →
                RawSymmetric.compose
                  (originalQuotientOrbital S (G := G) J a b)
                  T u v :=
          original_reset_Peirc_covers_external_layer
            S H J K hJK a b x y
            (Quotient.mk J.val x) (Quotient.mk J.val y)
            (originalQuotientOrbital_root S (G := G) J x y)
            hAll
        have hFull :
            RawSymmetric.compose
              (originalQuotientOrbital S (G := G) J a b) T =
                originalQuotientExternalLayer S J K hJK := by
          funext u v
          apply propext
          constructor
          · intro hComp
            have hKuv : originalUpperSetoid S J K hJK u v :=
              originalTwoQuotientOrbitals_comp_inside_upper
                S H J K hJK a b x y hab hKxy u v hComp
            have hNe : u ≠ v := by
              intro hEq
              subst v
              obtain ⟨mid,hM,hT⟩ := hComp
              have hCoincide :=
                (originalQuotientOrbital_two_return_iff_eq
                  S H J a b x y).mp ⟨u,mid,hM,hT⟩
              exact hTeq hCoincide.symm
            exact ⟨hKuv,hNe⟩
          · exact hContained u v
        exact False.elim (hNoMixedFull x y hKxy hNotJxy hTeq hFull)

/-- Complete SOURCE OWL-I, still inside the actual contradiction case:
the intersection of ALL actual P_C=M0;C over complete K-external
old-G quotient orbitals is precisely M0 itself. The easy inclusion
M0⊆P_C is the already proved C40 reset Peirce consequence; the
reverse is the genuinely proved orbit/disjointness argument above.

There is no extra conditional CCO/Helly provider, and the
`hNoMixedFull` assumption is explicitly the negation of the
desired distinct-orbit product, to be discharged by finite escape.
-/
theorem original_reset_external_intersection_iff
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (a b : X i) (hab : K a b)
    (hReset :
      RawSymmetric.compose
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
    (q r : Quotient J.val) :
    (∀ c d : X i, K c d → ¬ J c d →
      RawSymmetric.compose
        (originalQuotientOrbital S (G := G) J a b)
        (originalQuotientOrbital S (G := G) J c d) q r) ↔
      originalQuotientOrbital S (G := G) J a b q r := by
  constructor
  · exact original_reset_external_intersection_subset_orbital
      S H J K hJK a b hab hDifferent hNoMixedFull q r
  · intro hM c d hKcd _
    exact original_reset_orbital_subset_comp_every_K_orbital
      S H J K hJK a b c d hKcd hReset q r hM

end CCO.TerminalLattice
