import CCO.TerminalLattice.QuotientLift
import CCO.ParityHasse.Original.OrbitalAlgebra
import CCO.StabilizerSAP
import CCO.SAPPoint

/-!
# B050 C10: original SAP makes every nonidentity invariant fibre fresh

This is the missing ORIGINAL source instance of the explicitly conditional
`FreshFibre` used by the source-09 quotient STRONG semigroup. It uses
only actual finite-age SAP and original finite homogeneity, via the
accepted B001 theorem on pointwise-stabilizer orbit freshness.

No original CCO, NR2, FULL cover or quotient homogeneity is assumed.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Strictly nonidentity original invariant equivalences contain a
genuine ordered pair of DISTINCT original real points. -/
theorem actual_nontrivial_equiv_pair {i : ι}
    (J : ParityHasse.Original.ColourEq S i)
    (hJ : (⊥ : ParityHasse.Original.ColourEq S i) < J) :
    ∃ a b : X i, J a b ∧ a ≠ b := by
  have hnot : ¬ J ≤ (⊥ : ParityHasse.Original.ColourEq S i) :=
    not_le_of_gt hJ
  by_contra h
  apply hnot
  intro a b hab
  have hEq : a = b := by
    by_contra hne
    exact h ⟨a, b, hab, hne⟩
  exact hEq

/-- Original-source instance of B050 C10: each actual J-class can
avoid an ARBITRARY finite set of real old points. The original group
is the one acting on the whole named-sorted homogeneous source. -/
theorem freshFibre_of_original_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J : ParityHasse.Original.ColourEq S i)
    (hJ : (⊥ : ParityHasse.Original.ColourEq S i) < J) :
    FreshFibre J.val := by
  classical
  obtain ⟨c, d, hcd, hcdne⟩ := actual_nontrivial_equiv_pair S J hJ
  intro q forbidden
  induction q using Quotient.inductionOn with
  | _ a =>
    obtain ⟨g, hgc⟩ := S.original_sort_transitive_of_homogeneous H i c a
    let b : X i := g • d
    have hab : J a b := by
      have hmove :=
        ParityHasse.Original.colourInvariant_groupInvariant S H J.2 g c d hcd
      simpa only [hgc, b] using hmove
    have habne : a ≠ b := by
      intro heq
      have hcdeq : g • c = g • d := by
        simpa only [hgc, b] using heq
      exact hcdne (MulAction.injective g hcdeq)
    let anchor : Sigma X := ⟨i, a⟩
    let base : FiniteInduced (X := X) :=
      FiniteInduced.ofFinset ({anchor} : Finset (Sigma X))
    have hanchor : anchor ∈ base.vertices := by
      simp [base, FiniteInduced.ofFinset]
    have hbNot : (⟨i, b⟩ : Sigma X) ∉ base.vertices := by
      intro hb
      have hba : b = a := by
        simpa [base, FiniteInduced.ofFinset, anchor] using hb
      exact habne hba.symm
    let forbiddenTag : Set (Sigma X) :=
      (fun x : X i => (⟨i,x⟩ : Sigma X)) '' (↑forbidden : Set (X i))
    have hfinite : forbiddenTag.Finite := forbidden.finite_toSet.image _
    obtain ⟨yTag, hyOrbit, hyNot⟩ :=
      RealAction.orbit_has_fresh_point_of_SAP S H sap base
        (⟨i,b⟩ : Sigma X) hbNot forbiddenTag hfinite
    obtain ⟨k, hkFix, hkb⟩ := hyOrbit
    have hsort : yTag.1 = i := by
      calc
        yTag.1 = (k • (⟨i,b⟩ : Sigma X)).1 := congrArg Sigma.fst hkb.symm
        _ = i := by simp only [Sigma.smul_mk]
    obtain ⟨y, hyTag⟩ := tagged_exists_of_sort (X := X) yTag i hsort
    have hfixAnchor : k • anchor = anchor :=
      (RealAction.mem_pointwiseStabilizer base.vertices k).mp
        hkFix anchor hanchor
    have hka : k • a = a := by
      simpa only [anchor, Sigma.smul_mk, Sigma.mk.injEq,
        heq_eq_eq, true_and] using hfixAnchor
    have hky : k • b = y := by
      rw [hyTag] at hkb
      simpa only [Sigma.smul_mk, Sigma.mk.injEq,
        heq_eq_eq, true_and] using hkb
    have hay : J a y := by
      have hmove :=
        ParityHasse.Original.colourInvariant_groupInvariant S H J.2 k a b hab
      simpa only [hka, hky] using hmove
    refine ⟨y, ?_, ?_⟩
    · intro hy
      apply hyNot
      exact ⟨y, hy, hyTag.symm⟩
    · exact Quotient.sound (J.val.symm hay)

/-- B050 C11–C12, with original SAP now actually providing the
freshness required for quotient diagonal, injectivity and two-edge
STRONG composition. No B049 theorem is imported. -/
theorem original_quotient_semigroup
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J : ParityHasse.Original.ColourEq S i)
    (hJ : (⊥ : ParityHasse.Original.ColourEq S i) < J)
    (R T : Quotient J.val → Quotient J.val → Prop) :
    strongCompose (quotientDiversity J.val R) (quotientDiversity J.val T) =
      quotientDiversity J.val (RawSymmetric.compose R T) :=
  quotientDiversity_strong_comp J.val
    (freshFibre_of_original_SAP S H sap J hJ) R T

/-- The same source-derived, not hypothesized, fresh class property
makes the OLD nonempty quotient-diagonal diversity pullback injective. -/
theorem original_quotient_pullback_injective
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J : ParityHasse.Original.ColourEq S i)
    (hJ : (⊥ : ParityHasse.Original.ColourEq S i) < J) :
    Function.Injective (quotientDiversity J.val) :=
  quotientDiversity_injective J.val
    (freshFibre_of_original_SAP S H sap J hJ)

end CCO.TerminalLattice
