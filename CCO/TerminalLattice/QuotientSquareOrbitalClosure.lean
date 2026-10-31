import CCO.TerminalLattice.QuotientSquareSaturation

/-!
# B050 C37: a square meeting a COMPLETE old quotient orbital contains it

Let m be one complete quotient orbital of the SAME original full
automorphism group G on real J-classes. Its literal OLD fine-diversity
STRONG square W is already proved in C36 to be fully J-bisaturated
and invariant under the ORIGINAL G action.

This lemma does NOT assume or conclude the reset W=K^circ. Instead it
discharges the source's exact orbit-closure step: if W intersects any
other complete old quotient G-orbital T in ONE actual OLD fine atom,
then T is entirely contained in W. The proof aligns the two real
quotient endpoint pairs with ONE original G automorphism and then
uses the proved full-J saturation of W. No CCO, index-two assumption,
B049, abstract quotient homogeneity or invented fine-atom closure.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- Two pairs of ACTUAL old real representatives belonging to the
same COMPLETE original-G quotient orbital differ by ONE old G-motion
up to J at BOTH endpoints. This is not pair homogeneity of a larger
quotient reduct, and works for repeated quotient endpoint classes. -/
theorem original_quotient_orbital_pair_realign
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i)
    (p q x y u v : X i)
    (hXY : originalQuotientOrbital S (G := G) J p q
      (Quotient.mk J.val x) (Quotient.mk J.val y))
    (hUV : originalQuotientOrbital S (G := G) J p q
      (Quotient.mk J.val u) (Quotient.mk J.val v)) :
    ∃ k : G, J (k • x) u ∧ J (k • y) v := by
  letI : MulAction G (Quotient J.val) :=
    originalQuotientAction S H J
  obtain ⟨g, hgP, hgQ⟩ := hXY
  obtain ⟨h, hhP, hhQ⟩ := hUV
  have hgP' : g • Quotient.mk J.val p = Quotient.mk J.val x := hgP
  have hgQ' : g • Quotient.mk J.val q = Quotient.mk J.val y := hgQ
  have hhP' : h • Quotient.mk J.val p = Quotient.mk J.val u := hhP
  have hhQ' : h • Quotient.mk J.val q = Quotient.mk J.val v := hhQ
  refine ⟨h*g⁻¹, ?_, ?_⟩
  · apply Quotient.exact
    calc
      Quotient.mk J.val ((h*g⁻¹) • x) =
          (h*g⁻¹) • Quotient.mk J.val x := rfl
      _ = h • (g⁻¹ • Quotient.mk J.val x) := mul_smul _ _ _
      _ = h • Quotient.mk J.val p := by
        rw [← hgP', inv_smul_smul]
      _ = Quotient.mk J.val u := hhP'
  · apply Quotient.exact
    calc
      Quotient.mk J.val ((h*g⁻¹) • y) =
          (h*g⁻¹) • Quotient.mk J.val y := rfl
      _ = h • (g⁻¹ • Quotient.mk J.val y) := mul_smul _ _ _
      _ = h • Quotient.mk J.val q := by
        rw [← hgQ', inv_smul_smul]
      _ = Quotient.mk J.val v := hhQ'

/-- SOURCE C37 genuine complete-orbital closure of the OLD strong
square: ONE fine-colour intersection with an original quotient orbital
forces inclusion of the ENTIRE full-preimage OLD fine palette. Only
original homogeneous AgeSAP and J>Id are assumed; the square
bisaturation was PROVED, not postulated. No original CCO is consumed
here: it will be used exactly once later to supply such intersections
simultaneously via the private sparse graph. -/
theorem original_complete_square_meeting_orbital_contains_it
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (p q u v : X i)
    (hMeet :
      (S.product
        (originalQuotientOrbitalPalette S (G := G) J p q)
        (originalQuotientOrbitalPalette S (G := G) J p q)
        ∩ originalQuotientOrbitalPalette S (G := G) J u v).Nonempty) :
    originalQuotientOrbitalPalette S (G := G) J u v ⊆
      S.product
        (originalQuotientOrbitalPalette S (G := G) J p q)
        (originalQuotientOrbitalPalette S (G := G) J p q) := by
  let W : S.Menu i i :=
    S.product
      (originalQuotientOrbitalPalette S (G := G) J p q)
      (originalQuotientOrbitalPalette S (G := G) J p q)
  let V : S.Menu i i :=
    originalQuotientOrbitalPalette S (G := G) J u v
  obtain ⟨d, hdW, hdV⟩ := hMeet
  obtain ⟨x,y,hColXY⟩ := S.realized d
  have hOrbXY : originalQuotientOrbital S (G := G) J u v
      (Quotient.mk J.val x) (Quotient.mk J.val y) := by
    have hPair : S.menuRel V x y := ⟨d, hdV, hColXY⟩
    rw [originalQuotientOrbitalPalette_semantics S H J u v] at hPair
    exact hPair.2
  intro c hcV
  obtain ⟨a,b,hColAB⟩ := S.realized c
  have hOrbAB : originalQuotientOrbital S (G := G) J u v
      (Quotient.mk J.val a) (Quotient.mk J.val b) := by
    have hPair : S.menuRel V a b := ⟨c, hcV, hColAB⟩
    rw [originalQuotientOrbitalPalette_semantics S H J u v] at hPair
    exact hPair.2
  obtain ⟨g,hJX,hJY⟩ :=
    original_quotient_orbital_pair_realign
      S H J u v x y a b hOrbXY hOrbAB
  have hWMoved : S.menuRel W (g • x) (g • y) := by
    refine ⟨d, hdW, ?_⟩
    exact (S.colourInvariant_of_homogeneous H g x y).trans hColXY
  have hABne : a ≠ b := by
    intro hab
    exact S.atomRel_ne hColAB (congrArg (Sigma.mk i) hab)
  have hWAB : S.menuRel W a b :=
    original_complete_quotient_orbital_square_J_bisaturated
      S H sap J hJ p q (g • x) (g • y) a b hABne hJX hJY hWMoved
  obtain ⟨e, heW, hColE⟩ := hWAB
  have hEC : e = c := Option.some.inj (hColE.symm.trans hColAB)
  exact hEC ▸ heW

end CCO.TerminalLattice
