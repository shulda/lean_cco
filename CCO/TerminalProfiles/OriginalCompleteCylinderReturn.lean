import CCO.TerminalLattice.OriginalQuotientOrbitalReturn
import CCO.TerminalLattice.StrongPaletteBridge
import CCO.TerminalLattice.FibreSAP
import Mathlib.Data.Finset.Basic

/-!
# B051 — SOURCE09 JRT: genuine complete OLD quotient cylinders return

Each cylinder below is the FULL diversity pullback of ONE original-G
pair-orbital on the true old J-quotient, not a union of several such
orbitals. The two chosen old pairs are external to J; J > Id ensures
fresh old real representatives even when a quotient-class walk closes.

The forward implication reads a three-distinct-point STRONG triangle,
uses actual FULL J-equivalence to close its quotient endpoints, then
uses the accepted B050 complete-orbital two-return theorem.
Conversely, the orbit equality plus original SAP's genuine fresh J
fibre supplies three distinct old points. Their pair colours form the
required STRONG triangle with its output in J°.

No CCO, FULL NR2, exactness, positive-word presentation, quotient SAP
or synthetic STRONG equality atom is assumed.
-/

universe u v w t

namespace CCO.TerminalProfiles

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- SOURCE09 C19–C22, JRT for two genuine external COMPLETE original
quotient orbitals, stated with their actual old pair representatives.
Equality refers to the full old diversity cylinders, NOT arbitrary
J-bisaturated unions. The two end pairs lie outside J. -/
theorem original_complete_J_cylinders_return_iff_eq
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (a b c d : X i)
    (hab : ¬ J a b) (_hcd : ¬ J c d) :
    ((S.product
      (originalQuotientOrbitalPalette S (G := G) J a b)
      (originalQuotientOrbitalPalette S (G := G) J c d)) ∩
        originalEquivDiversityPalette S J).Nonempty ↔
      originalQuotientOrbitalPalette S (G := G) J a b =
        originalQuotientOrbitalPalette S (G := G) J c d := by
  classical
  let T : S.Menu i i :=
    originalQuotientOrbitalPalette S (G := G) J a b
  let U : S.Menu i i :=
    originalQuotientOrbitalPalette S (G := G) J c d
  let E : S.Menu i i := originalEquivDiversityPalette S J
  change (S.product T U ∩ E).Nonempty ↔ T = U
  constructor
  · rintro ⟨s, ⟨t₁, ht₁, t₂, ht₂, x, y, z, hxy, hyz, hxz⟩, hs⟩
    have hJxz : J x z := by
      obtain ⟨v, w, hJvw, hvws⟩ := hs
      exact (J.property v w x z (hvws.trans hxz.symm)).mp hJvw
    have hTxy : S.menuRel T x y := ⟨t₁, ht₁, hxy⟩
    have hUyz : S.menuRel U y z := ⟨t₂, ht₂, hyz⟩
    have hOrbT : originalQuotientOrbital S (G := G) J a b
        (Quotient.mk J.val x) (Quotient.mk J.val y) := by
      rw [originalQuotientOrbitalPalette_semantics S H J a b] at hTxy
      exact hTxy.2
    have hOrbU : originalQuotientOrbital S (G := G) J c d
        (Quotient.mk J.val y) (Quotient.mk J.val z) := by
      rw [originalQuotientOrbitalPalette_semantics S H J c d] at hUyz
      exact hUyz.2
    have hzEq : Quotient.mk J.val z = Quotient.mk J.val x :=
      Quotient.sound (J.val.symm hJxz)
    have hTwo : originalQuotientOrbital S (G := G) J c d
        (Quotient.mk J.val y) (Quotient.mk J.val x) := by
      simpa only [hzEq] using hOrbU
    have hOrbitEq : originalQuotientOrbital S (G := G) J a b =
        originalQuotientOrbital S (G := G) J c d :=
      (originalQuotientOrbital_two_return_iff_eq
        S H J a b c d).mp
          ⟨Quotient.mk J.val x, Quotient.mk J.val y, hOrbT, hTwo⟩
    change originalQuotientOrbitalPalette S (G := G) J a b =
      originalQuotientOrbitalPalette S (G := G) J c d
    rw [originalQuotientOrbitalPalette, hOrbitEq]
    rfl
  · intro hTU
    have hMenus : S.menuRel T = S.menuRel U :=
      congrArg (fun M : S.Menu i i => S.menuRel M) hTU
    have hQeq :
        quotientDiversity J.val (originalQuotientOrbital S (G := G) J a b) =
        quotientDiversity J.val (originalQuotientOrbital S (G := G) J c d) :=
      (originalQuotientOrbitalPalette_semantics S H J a b).symm.trans
        (hMenus.trans (originalQuotientOrbitalPalette_semantics S H J c d))
    have hOrbitEq : originalQuotientOrbital S (G := G) J a b =
        originalQuotientOrbital S (G := G) J c d :=
      original_quotient_pullback_injective S H sap J hJ hQeq
    have habNe : a ≠ b := by
      intro h
      subst b
      exact hab (J.val.refl a)
    have hOrbRoot : originalQuotientOrbital S (G := G) J a b
        (Quotient.mk J.val a) (Quotient.mk J.val b) :=
      originalQuotientOrbital_root S (G := G) J a b
    obtain ⟨z, hzFresh, hzEq⟩ :=
      (freshFibre_of_original_SAP S H sap J hJ)
        (Quotient.mk J.val a) ({a} : Finset (X i))
    have hazNe : a ≠ z := by
      intro h
      apply hzFresh
      exact Finset.mem_singleton.mpr h.symm
    have hJaz : J a z := Quotient.exact hzEq.symm
    have hbzNe : b ≠ z := by
      intro h
      apply hab
      simpa only [h] using hJaz
    have hOrbU : originalQuotientOrbital S (G := G) J c d
        (Quotient.mk J.val b) (Quotient.mk J.val z) := by
      rw [← hOrbitEq, hzEq]
      exact originalQuotientOrbital_symmetric
        S H J a b _ _ hOrbRoot
    have hTab : S.menuRel T a b := by
      change S.menuRel
        (originalQuotientOrbitalPalette S (G := G) J a b) a b
      rw [originalQuotientOrbitalPalette_semantics S H J a b]
      exact ⟨habNe, hOrbRoot⟩
    have hUbz : S.menuRel U b z := by
      change S.menuRel
        (originalQuotientOrbitalPalette S (G := G) J c d) b z
      rw [originalQuotientOrbitalPalette_semantics S H J c d]
      exact ⟨hbzNe, hOrbU⟩
    obtain ⟨t₁, ht₁, htab⟩ := hTab
    obtain ⟨t₂, ht₂, htbz⟩ := hUbz
    have hTagged : (⟨i, a⟩ : Sigma X) ≠ ⟨i, z⟩ := by
      intro h
      have heq : a = z := by
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h
      exact hazNe heq
    obtain ⟨s, has⟩ := S.some_colour_of_ne a z hTagged
    have hsE : s ∈ E := ⟨a, z, hJaz, has⟩
    exact ⟨s, ⟨t₁, ht₁, t₂, ht₂, a, b, z, htab, htbz, has⟩, hsE⟩

end CCO.TerminalProfiles
