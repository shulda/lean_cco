import CCO.TerminalLattice.OriginalFullCoverReset

/-!
# B050 source09 C45: two-edge returns of COMPLETE original quotient G-orbitals

One and the same ORIGINAL ambient group G acts on old J-classes. We
prove the elementary, exact complete-orbital intersection property
directly for its diagonal action on pairs. This is NOT a quotient
homogeneity assumption or a new quotient group.

In a symmetric original source, a two-edge quotient return using
two COMPLETE G-orbitals is possible iff those orbitals coincide.
Thus distinct external complete orbitals cannot make quotient
diagonal pairs by one composition. The statement is strictly for
complete orbitals, not arbitrary invariant unions.
-/

universe u v w t z

namespace CCO.TerminalLattice

/-- Pair orbits of the SAME group action that share an actual ordered
pair coincide globally. Only the group laws and action laws enter. -/
private theorem original_group_pair_orbit_eq_of_overlap
    {Q : Type z} {G : Type t} [Group G] [MulAction G Q]
    (a b c d q r : Q)
    (hFirst : ∃ g : G, g • a = q ∧ g • b = r)
    (hSecond : ∃ g : G, g • c = q ∧ g • d = r) :
    (fun x y : Q => ∃ g : G, g • a = x ∧ g • b = y) =
      (fun x y : Q => ∃ g : G, g • c = x ∧ g • d = y) := by
  obtain ⟨g,hga,hgb⟩ := hFirst
  obtain ⟨h,hhc,hhd⟩ := hSecond
  funext x y
  apply propext
  constructor
  · rintro ⟨k,hka,hkb⟩
    refine ⟨k * (g⁻¹ * h), ?_, ?_⟩
    · calc
        (k * (g⁻¹ * h)) • c = k • (g⁻¹ • (h • c)) := by rw [mul_smul,mul_smul]
        _ = k • (g⁻¹ • (g • a)) := by rw [hhc,←hga]
        _ = k • a := by rw [inv_smul_smul]
        _ = x := hka
    · calc
        (k * (g⁻¹ * h)) • d = k • (g⁻¹ • (h • d)) := by rw [mul_smul,mul_smul]
        _ = k • (g⁻¹ • (g • b)) := by rw [hhd,←hgb]
        _ = k • b := by rw [inv_smul_smul]
        _ = y := hkb
  · rintro ⟨k,hkc,hkd⟩
    refine ⟨k * (h⁻¹ * g), ?_, ?_⟩
    · calc
        (k * (h⁻¹ * g)) • a = k • (h⁻¹ • (g • a)) := by rw [mul_smul,mul_smul]
        _ = k • (h⁻¹ • (h • c)) := by rw [hga,←hhc]
        _ = k • c := by rw [inv_smul_smul]
        _ = x := hkc
    · calc
        (k * (h⁻¹ * g)) • b = k • (h⁻¹ • (g • b)) := by rw [mul_smul,mul_smul]
        _ = k • (h⁻¹ • (h • d)) := by rw [hgb,←hhd]
        _ = k • d := by rw [inv_smul_smul]
        _ = y := hkd

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- For the actual induced action on original J-classes, an
intersection of TWO full original-G quotient pair orbits forces
their equality everywhere, even when the intersecting pair happens
to lie on the quotient diagonal. No H-reduct automorphism is used. -/
theorem originalQuotientOrbital_eq_of_overlap
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (a b c d : X i)
    (q r : Quotient J.val)
    (hFirst : originalQuotientOrbital S (G := G) J a b q r)
    (hSecond : originalQuotientOrbital S (G := G) J c d q r) :
    originalQuotientOrbital S (G := G) J a b =
      originalQuotientOrbital S (G := G) J c d := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  obtain ⟨g,hga,hgb⟩ := hFirst
  obtain ⟨h,hhc,hhd⟩ := hSecond
  have hFirst' :
      ∃ g : G, g • Quotient.mk J.val a = q ∧
        g • Quotient.mk J.val b = r := by
    refine ⟨g, ?_, ?_⟩
    · simpa only [originalQuotient_mk_smul S H J] using hga
    · simpa only [originalQuotient_mk_smul S H J] using hgb
  have hSecond' :
      ∃ h : G, h • Quotient.mk J.val c = q ∧
        h • Quotient.mk J.val d = r := by
    refine ⟨h, ?_, ?_⟩
    · simpa only [originalQuotient_mk_smul S H J] using hhc
    · simpa only [originalQuotient_mk_smul S H J] using hhd
  have hEq := original_group_pair_orbit_eq_of_overlap
    (Quotient.mk J.val a) (Quotient.mk J.val b)
    (Quotient.mk J.val c) (Quotient.mk J.val d)
    q r hFirst' hSecond'
  change originalQuotientOrbital S (G := G) J a b =
    originalQuotientOrbital S (G := G) J c d at hEq
  exact hEq

/-- SOURCE C45 exact complete-orbital quotient two-return test:
a two-step quotient closed walk using two complete old-G orbitals
exists iff those orbitals are literally the SAME complete orbital.
The return is a REAL quotient relation product; there is no old
strong diversity identity atom. -/
theorem originalQuotientOrbital_two_return_iff_eq
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (a b c d : X i) :
    (∃ q r : Quotient J.val,
      originalQuotientOrbital S (G := G) J a b q r ∧
      originalQuotientOrbital S (G := G) J c d r q) ↔
    originalQuotientOrbital S (G := G) J a b =
      originalQuotientOrbital S (G := G) J c d := by
  constructor
  · rintro ⟨q,r,hFirst,hSecond⟩
    exact originalQuotientOrbital_eq_of_overlap
      S H J a b c d q r hFirst
      (originalQuotientOrbital_symmetric S H J c d r q hSecond)
  · intro heq
    refine ⟨Quotient.mk J.val a, Quotient.mk J.val b,
      originalQuotientOrbital_root S (G := G) J a b, ?_⟩
    rw [← heq]
    exact originalQuotientOrbital_symmetric
      S H J a b _ _ (originalQuotientOrbital_root S (G := G) J a b)

/-- Distinct COMPLETE original ambient-G quotient orbitals have no
two-edge closed return. In particular their original quotient
composition is disjoint from the TRUE quotient diagonal. This
does NOT assert the same for arbitrary invariant unions. -/
theorem originalQuotientOrbital_distinct_no_two_return
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (a b c d : X i)
    (hne : originalQuotientOrbital S (G := G) J a b ≠
      originalQuotientOrbital S (G := G) J c d) :
    ∀ q : Quotient J.val,
      ¬ ∃ mid : Quotient J.val,
        originalQuotientOrbital S (G := G) J a b q mid ∧
        originalQuotientOrbital S (G := G) J c d mid q := by
  intro q ⟨mid,hFirst,hSecond⟩
  exact hne ((originalQuotientOrbital_two_return_iff_eq
    S H J a b c d).mp ⟨q,mid,hFirst,hSecond⟩)

end CCO.TerminalLattice
