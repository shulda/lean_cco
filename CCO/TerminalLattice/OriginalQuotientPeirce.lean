import CCO.TerminalLattice.OriginalKPositiveFromExternal
import CCO.TerminalLattice.OriginalQuotientInvariantFinite

/-!
# B050 source09 OWL-I: genuine Peirce rotation and full-orbital containment

The finite external-layer escape argument is carried out on the TRUE
quotient of the old real sort by J, with the induced action of the
ORIGINAL ambient automorphism group. This file proves two elementary
but essential facts about the precise complete old-G quotient orbitals.

(1) For a symmetric relation M, an actual witness to
    (M ; C) intersect D can be rotated to (M ; D) intersect C,
    without altering the intermediate quotient point.
(2) An ORIGINAL-G-invariant relation meeting one complete old-G pair
    orbital contains the ENTIRE orbital, by an actual group element
    sending one concrete orbit pair to the other.

As a first consequence of the already-proved C40 reset, the complete
external reset orbital M0 lies inside M0 ; C for EVERY actual
K-related complete quotient orbital C. This is the first exact step
of OWL-I, not a conditional reset provider or the final external-layer
word theorem.

No quotient-reduct automorphisms, quotient SAP/CCO, diagonal deletion,
new source hypotheses or extra axioms.
-/

universe u v w t

namespace CCO.TerminalLattice

/-- Genuine Peirce rotation of a nonempty intersection of two binary
relation products on the SAME quotient carrier. Only M needs to be
symmetric; the other relations may be arbitrary, including true
quotient-diagonal states. -/
theorem original_peirce_intersection
    {Q : Type*} (M C D : Q → Q → Prop)
    (hSymm : ∀ x y, M x y → M y x) :
    (∃ x y : Q, RawSymmetric.compose M C x y ∧ D x y) ↔
      (∃ x y : Q, RawSymmetric.compose M D x y ∧ C x y) := by
  constructor
  · rintro ⟨x,y,⟨z,hxz,hzy⟩,hD⟩
    exact ⟨z,y,⟨x,hSymm x z hxz,hD⟩,hzy⟩
  · rintro ⟨z,y,⟨x,hzx,hxy⟩,hC⟩
    exact ⟨x,y,⟨z,hSymm z x hzx,hC⟩,hxy⟩

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- A real intersection with a COMPLETE pair orbit under the OLD
ambient group makes the whole orbit lie in the invariant state.
This is proved with the explicit group transport h*g⁻¹ between
witnesses, rather than postulating a homogeneous quotient reduct. -/
theorem original_complete_quotient_orbital_subset_of_invariant_meeting
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i)
    (a b : X i)
    (T : OriginalInvariantQuotientState S H J)
    (hMeet : ∃ q r : Quotient J.val,
      originalQuotientOrbital S (G := G) J a b q r ∧ T.val q r) :
    ∀ q r : Quotient J.val,
      originalQuotientOrbital S (G := G) J a b q r → T.val q r := by
  letI : MulAction G (Quotient J.val) :=
    originalQuotientAction S H J
  obtain ⟨q0,r0,⟨g,hgq,hgr⟩,hT⟩ := hMeet
  intro q r
  rintro ⟨h,hhq,hhr⟩
  have hBaseQ : g • Quotient.mk J.val a = q0 := by
    simpa only [originalQuotient_mk_smul S H J] using hgq
  have hBaseR : g • Quotient.mk J.val b = r0 := by
    simpa only [originalQuotient_mk_smul S H J] using hgr
  have hTargetQ : h • Quotient.mk J.val a = q := by
    simpa only [originalQuotient_mk_smul S H J] using hhq
  have hTargetR : h • Quotient.mk J.val b = r := by
    simpa only [originalQuotient_mk_smul S H J] using hhr
  have hMoveQ : (h*g⁻¹) • q0 = q := by
    calc
      (h*g⁻¹) • q0 = (h*g⁻¹) • (g • Quotient.mk J.val a) := by
        rw [hBaseQ]
      _ = h • Quotient.mk J.val a := by
        rw [mul_smul,inv_smul_smul]
      _ = q := hTargetQ
  have hMoveR : (h*g⁻¹) • r0 = r := by
    calc
      (h*g⁻¹) • r0 = (h*g⁻¹) • (g • Quotient.mk J.val b) := by
        rw [hBaseR]
      _ = h • Quotient.mk J.val b := by
        rw [mul_smul,inv_smul_smul]
      _ = r := hTargetR
  have hTmove := T.property (h*g⁻¹) q0 r0 hT
  rw [hMoveQ,hMoveR] at hTmove
  exact hTmove

/-- First exact OWL-I consequence of the already PROVED original C40:
if the square of the COMPLETE external original-G orbital M0 is
the entire K/J quotient relation, then for EVERY real K-pair c,d,
the ENTIRE reset orbit M0 lies in its product with the complete
original-G pair orbital C(c,d).

The input M0;M0 = K/J is obtained unconditionally from original
CCO+SAP in `original_full_cover_quotient_reset_of_Jpositive`.
There is no assumption that a proper fine suborbital is complete,
or that the quotient has an independently enlarged automorphism group.
-/
theorem original_reset_orbital_subset_comp_every_K_orbital
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (a b c d : X i)
    (hKcd : K c d)
    (hReset :
      RawSymmetric.compose
        (originalQuotientOrbital S (G := G) J a b)
        (originalQuotientOrbital S (G := G) J a b) =
          (originalUpperSetoid S J K hJK).r) :
    ∀ q r : Quotient J.val,
      originalQuotientOrbital S (G := G) J a b q r →
        RawSymmetric.compose
          (originalQuotientOrbital S (G := G) J a b)
          (originalQuotientOrbital S (G := G) J c d) q r := by
  let M : Quotient J.val → Quotient J.val → Prop :=
    originalQuotientOrbital S (G := G) J a b
  let C : Quotient J.val → Quotient J.val → Prop :=
    originalQuotientOrbital S (G := G) J c d
  let MState : OriginalInvariantQuotientState S H J :=
    ⟨M,originalQuotientOrbital_invariant S H J a b⟩
  let CState : OriginalInvariantQuotientState S H J :=
    ⟨C,originalQuotientOrbital_invariant S H J c d⟩
  let P := originalInvariantQuotientState_comp S H J MState CState
  have hUpper : originalUpperSetoid S J K hJK
      (Quotient.mk J.val c) (Quotient.mk J.val d) :=
    (originalUpperSetoid_mk S J K hJK c d).mpr hKcd
  have hTwo : RawSymmetric.compose M M
      (Quotient.mk J.val c) (Quotient.mk J.val d) := by
    rw [hReset]
    exact hUpper
  obtain ⟨z,hCZ,hZD⟩ := hTwo
  have hMZ : M z (Quotient.mk J.val d) := hZD
  have hPZ : P.val z (Quotient.mk J.val d) := by
    exact ⟨Quotient.mk J.val c,
      originalQuotientOrbital_symmetric
        S H J a b _ _ hCZ,
      originalQuotientOrbital_root S (G := G) J c d⟩
  have hInclusion :=
    original_complete_quotient_orbital_subset_of_invariant_meeting
      S H J a b P ⟨z,Quotient.mk J.val d,hMZ,hPZ⟩
  intro q r hMqr
  exact hInclusion q r hMqr

end CCO.TerminalLattice
