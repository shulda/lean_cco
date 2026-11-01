import CCO.TransitionClosure.OriginalQuotientSaturation

/-!
# B049 source07 C11-C13: actual quotient-diagonal and K-cut witnesses

The original first-hit proof assumes a positive OLD profile P that
MEETS J-diversity, EXITS J and avoids the external K\J layer.
Its genuine J-bisaturation S has the full quotient state ̅S built
in OriginalQuotientSaturation, not a selected proper fine subset.

These source-faithful preliminary lemmas establish the three basic
facts directly from actual old colour orbitals:
* the TRUE quotient diagonal Δ_{M_a/J} lies entirely in ̅S
  if P meets J°;
* ̅S has at least one genuine off-diagonal quotient edge
  if P has an atom outside J°;
* if P avoids K°\J°, then ̅S has ONLY the diagonal inside K/J.

No assumed MI, FULL cover, old CCO, quotient SAP, invented STRONG
identity or new source hypothesis is used in these elementary
geometric implications. They are later combined with actual
full-cover connectedness and the first-hit power argument.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- True quotient-diagonal inclusion from one ACTUAL fine OLD atom
in P ∩ J°. Every original J-class is a quotient point; old
homogeneity moves the witnessing old J-pair to ANY such class.
Old equality is never installed as an STRONG word letter. -/
theorem originalJMenuQuotientState_contains_diagonal
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i) (P : S.Menu i i)
    (hMeet : (P ∩ originalEquivDiversityPalette S J).Nonempty) :
    ∀ q : Quotient J.val, originalJMenuQuotientState S J P q q := by
  obtain ⟨a,ha,hJAtom⟩ := hMeet
  obtain ⟨x,y,hJxy,hxy⟩ := hJAtom
  intro q
  induction q using Quotient.inductionOn with
  | _ z =>
      obtain ⟨g,hgx⟩ :=
        S.original_sort_transitive_of_homogeneous H i x z
      have hMovedJ : J (g • x) (g • y) :=
        colourInvariant_groupInvariant S H J.2 g x y hJxy
      have hJzy : J z (g • y) := by
        simpa only [hgx] using hMovedJ
      have hMovedColour : S.colour z (g • y) = some a := by
        have hMove := S.colourInvariant_of_homogeneous H g x y
        simpa only [hgx] using hMove.trans hxy
      exact ⟨z, g • y, rfl, Quotient.sound hJzy,
        ⟨a,ha,hMovedColour⟩⟩

/-- A genuine fine OLD atom outside J° is represented by an
OFF-DIAGONAL pair of actual J-classes in the same quotient state.
This does not assume P is one complete quotient orbital, only
that the old source realizes each of its named fine atoms. -/
theorem originalJMenuQuotientState_has_offdiagonal
    {i : ι} (J : ColourEq S i) (P : S.Menu i i)
    (hExit : ∃ a : S.Atom i i,
      a ∈ P ∧ a ∉ originalEquivDiversityPalette S J) :
    ∃ q r : Quotient J.val,
      q ≠ r ∧ originalJMenuQuotientState S J P q r := by
  obtain ⟨a,ha,hNotJ⟩ := hExit
  obtain ⟨x,y,hxy⟩ := S.realized a
  have hJxy : ¬ J x y := by
    intro hJ
    exact hNotJ ⟨x,y,hJ,hxy⟩
  refine ⟨Quotient.mk J.val x, Quotient.mk J.val y, ?_,
    x, y, rfl, rfl, ⟨a,ha,hxy⟩⟩
  intro hq
  exact hJxy (Quotient.exact hq)

/-- Original source first-hit gate: if P has NO K-external OLD
fine atom (in the precise sense that every P atom in K° already
lies in J°), then its genuine saturated quotient state cannot
have a K/J off-diagonal pair.

This is the exact source OWI-S geometry, with TRUE quotient
diagonal retained. No FULL cover/MI or old CCO enters. -/
theorem originalJMenuQuotientState_K_inside_diagonal
    {i : ι} (J K : ColourEq S i)
    (hJK : J ≤ K) (P : S.Menu i i)
    (hAvoid : ∀ a : S.Atom i i,
      a ∈ P →
      a ∈ originalEquivDiversityPalette S K →
      a ∈ originalEquivDiversityPalette S J)
    (x y : X i) (hKxy : K x y)
    (hState : originalJMenuQuotientState S J P
      (Quotient.mk J.val x) (Quotient.mk J.val y)) :
    J x y := by
  obtain ⟨u,v,hux,hvy,a,ha,hAtom⟩ := hState
  have hJux : J u x := Quotient.exact hux
  have hJvy : J v y := Quotient.exact hvy
  have hKuv : K u v := by
    exact K.val.trans
      (K.val.trans (hJK hJux) hKxy)
      (K.val.symm (hJK hJvy))
  have hKAtom :
      a ∈ originalEquivDiversityPalette S K :=
    ⟨u,v,hKuv,hAtom⟩
  obtain ⟨x0,y0,hJx0y0,hCol0⟩ :=
    hAvoid a ha hKAtom
  have hJuv : J u v :=
    (J.property x0 y0 u v (hCol0.trans hAtom.symm)).mp hJx0y0
  exact J.val.trans (J.val.trans (J.val.symm hJux) hJuv) hJvy

end CCO.TransitionClosure
