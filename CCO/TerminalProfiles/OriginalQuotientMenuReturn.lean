import CCO.TransitionClosure.OriginalQuotientSaturation
import CCO.TerminalLattice.OriginalModularity
import CCO.TerminalLattice.OriginalQuotientInvariantFinite
import CCO.TerminalLattice.StrongPaletteBridge

/-!
# B051 TNR C05–C09: the ACTUAL original J-menu quotient states

An arbitrary original diversity menu P is contained in its full
original RAW J;P;J saturation by reflexivity of the FULL J relation,
even when P is not contained in J°. The accepted B049 source theorem
then identifies that full saturation with the STRONG J°*P*J° menu.
This must NOT be inferred from equivalence reproduction C⊆J°.

The genuine original-G quotient relation of P is
  q R_P r iff SOME actual old P-edge connects representatives.
It is symmetric, serial when P is nonempty, and invariant under the
literal original action on X_i/J.

If P*Q⊆J°, the REAL original same-sort RAW commutation
J;Q=Q;J and the old three-distinct-vertices STRONG product semantics
show R_P;R_Q⊆Delta_{X_i/J}; no hypothetical quotient SAP or
simultaneous representative section is used.

The local no-index-two groupoid contradiction is a SEPARATE theorem.
-/

universe u v w t

namespace CCO.TerminalProfiles

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original
open CCO.TerminalLattice
open CCO.TransitionClosure

/-- The literal old source09 C05 saturation inclusion uses RAW
reflexivity, not a C⊆J° equivalence-reproduction hypothesis. -/
theorem original_menu_subset_full_J_saturation
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (P : S.Menu i i) :
    P ⊆ S.product (originalEquivDiversityPalette S J)
      (S.product P (originalEquivDiversityPalette S J)) := by
  intro a ha
  obtain ⟨x,y,hxy⟩ := S.realized a
  have hRaw : a ∈ S.diversityGuard (originalRawJMenuSandwich S J P) :=
    ⟨x,y,⟨x,y,J.val.refl x,⟨a,ha,hxy⟩,J.val.refl y⟩,hxy⟩
  rw [original_raw_J_menu_J_guard_eq_strong S H sap J hJ P] at hRaw
  exact hRaw

private theorem original_menu_colour_invariant
    {i : ι} (P : S.Menu i i) :
    ColourInvariant S i (S.menuRel P) := by
  intro x y x' y' hcol
  constructor
  · rintro ⟨a,ha,hxy⟩
    exact ⟨a,ha,hcol.symm.trans hxy⟩
  · rintro ⟨a,ha,hx'y'⟩
    exact ⟨a,ha,hcol.trans hx'y'⟩

/-- Every original menu quotient relation is symmetric because all
original SAME-SORT diversity orbitals are symmetric. -/
theorem original_quotient_menu_symmetric
    {i : ι} (J : ColourEq S i) (P : S.Menu i i) :
    ∀ q r : Quotient J.val,
      originalJMenuQuotientState S J P q r →
      originalJMenuQuotientState S J P r q := by
  intro q r
  rintro ⟨x,y,hx,hy,a,ha,hxy⟩
  refine ⟨y,x,hy,hx,a,ha,?_⟩
  have hMove := (S.colour_swap x y a).mp hxy
  simpa only [S.symmetricLoop a] using hMove

/-- Nonempty menus yield total quotient relations by original-sort
transitivity. No new quotient action or quotient SAP is assumed. -/
theorem original_quotient_menu_serial
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i)
    (P : S.Menu i i) (hP : P.Nonempty) :
    ∀ q : Quotient J.val,
      ∃ r, originalJMenuQuotientState S J P q r := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
    obtain ⟨a,ha⟩ := hP
    obtain ⟨u,v,huv⟩ := S.realized a
    obtain ⟨g,hgx⟩ :=
      S.original_sort_transitive_of_homogeneous H i u x
    have hxv : S.menuRel P x (g • v) := by
      refine ⟨a,ha,?_⟩
      have hcol := S.colourInvariant_of_homogeneous H g u v
      simpa only [hgx] using hcol.trans huv
    exact ⟨Quotient.mk J.val (g • v), x, g • v,
      rfl, rfl, hxv⟩

/-- The true old-G action, and NO hypothetical lift of quotient
automorphisms, preserves the existential original-menu quotient state. -/
theorem original_quotient_menu_invariant
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i) (P : S.Menu i i) :
    letI : MulAction G (Quotient J.val) :=
      originalQuotientAction S H J
    ∀ (g : G) (q r : Quotient J.val),
      originalJMenuQuotientState S J P q r →
      originalJMenuQuotientState S J P (g • q) (g • r) := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  intro g q r
  rintro ⟨x,y,hx,hy,a,ha,hxy⟩
  refine ⟨g • x,g • y,?_,?_,a,ha,?_⟩
  · calc
      Quotient.mk J.val (g • x) = g • Quotient.mk J.val x :=
        (originalQuotient_mk_smul S H J g x).symm
      _ = g • q := congrArg (fun z => g • z) hx
  · calc
      Quotient.mk J.val (g • y) = g • Quotient.mk J.val y :=
        (originalQuotient_mk_smul S H J g y).symm
      _ = g • r := congrArg (fun z => g • z) hy
  · exact (S.colourInvariant_of_homogeneous H g x y).trans hxy

/-- SOURCE09 C06: if the OLD two-factor STRONG profile stays in
original J°, then the product of the LITERAL original-G quotient
P/Q states lies in the TRUE quotient diagonal. The proof can align
a middle old J-class via J;Q=Q;J, without choosing representatives
of unrelated quotients, and uses actual RAW/STRONG at distinct
original endpoints. No quotient SAP or index exclusion. -/
theorem original_quotient_menu_comp_subset_diagonal
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i)
    (P Q : S.Menu i i)
    (hProduct : S.product P Q ⊆
      originalEquivDiversityPalette S J) :
    ∀ (q r s : Quotient J.val),
      originalJMenuQuotientState S J P q r →
      originalJMenuQuotientState S J Q r s →
      q = s := by
  intro q r s
  rintro ⟨x,y,hx,hy,hPxy⟩ ⟨u,v,hu,hv,hQuv⟩
  have hJyu : J y u := Quotient.exact (hy.trans hu.symm)
  have hComm : RawSymmetric.compose J.val.r (S.menuRel Q) =
      RawSymmetric.compose (S.menuRel Q) J.val.r :=
    original_raw_commutation S H J.val.r (S.menuRel Q)
      J.property (original_menu_colour_invariant S Q)
  have hJQ : RawSymmetric.compose J.val.r (S.menuRel Q) y v :=
    ⟨u,hJyu,hQuv⟩
  rw [hComm] at hJQ
  obtain ⟨w,hQyw,hJwv⟩ := hJQ
  have hJxw : J x w := by
    by_cases hEq : x = w
    · subst w
      exact J.val.refl x
    · have hxyNe : x ≠ y := by
        intro h
        exact (S.menuRel_ne hPxy) (congrArg (Sigma.mk i) h)
      have hywNe : y ≠ w := by
        intro h
        exact (S.menuRel_ne hQyw) (congrArg (Sigma.mk i) h)
      have hStrong : strongCompose (S.menuRel P)
          (S.menuRel Q) x w :=
        ⟨hEq,y,hxyNe,hywNe,hPxy,hQyw⟩
      have hMenu : S.menuRel (S.product P Q) x w := by
        rw [menuRel_product_eq_strongCompose S H P Q]
        exact hStrong
      obtain ⟨a,ha,hCol⟩ := hMenu
      obtain ⟨b,c,hJbc,hColBC⟩ := hProduct ha
      exact (J.property b c x w (hColBC.trans hCol.symm)).mp hJbc
  have hJxv : J x v := J.val.trans hJxw hJwv
  calc
    q = Quotient.mk J.val x := hx.symm
    _ = Quotient.mk J.val v := Quotient.sound hJxv
    _ = s := hv

end CCO.TerminalProfiles
