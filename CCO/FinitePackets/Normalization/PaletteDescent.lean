import CCO.RawExact.QuotientSourcePalette
import Mathlib.Data.Fintype.Card

/-! C23: an actual equivariant surjection cannot split an old orbital.
If its kernel is nonidentity, old equality and an old diversity colour
both map to output equality, so the CURRENT diversity palette drops.
No exactness, quotient homogeneity, CCO, or finite-class premise. -/
universe v w q r t
namespace CCO.FinitePackets.Normalization
variable {M : Type v} {N : Type q}
variable (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (T : AtomicSource.{0,q,r} Unit (fun _ => N))
variable {G : Type t} [Group G] [MulAction G M] [MulAction G N]
variable (H : HomogeneousSource S G)
variable (π : M → N) (hπ : Function.Surjective π)
variable (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
variable (invariantT : ∀ (g : G) x y, T.colour (i := ()) (j := ()) (g • x) (g • y) = T.colour (i := ()) (j := ()) x y)

noncomputable def quotientColourMap (c : Option (S.Atom () ())) :
    Option (T.Atom () ()) :=
  T.colour (i := ()) (j := ()) (π (RawExact.QuotientPalette.colourRepresentatives S c).1)
    (π (RawExact.QuotientPalette.colourRepresentatives S c).2)

include H equivπ invariantT

theorem quotientColourMap_at (x y : M) :
    quotientColourMap S T π (S.colour (i := ()) (j := ()) x y) = T.colour (i := ()) (j := ()) (π x) (π y) := by
  let c := S.colour (i := ()) (j := ()) x y
  have hc := RawExact.QuotientPalette.colourRepresentatives_spec S c
  obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H
    (RawExact.QuotientPalette.colourRepresentatives S c).1 x
    (RawExact.QuotientPalette.colourRepresentatives S c).2 y hc
  unfold quotientColourMap
  change T.colour (i := ()) (j := ()) (π (RawExact.QuotientPalette.colourRepresentatives S c).1)
    (π (RawExact.QuotientPalette.colourRepresentatives S c).2) = _
  rw [← hgx,← hgy,equivπ,equivπ]
  exact (invariantT g _ _).symm

include hπ in
theorem quotientColourMap_surjective : Function.Surjective (quotientColourMap S T π) := by
  intro c
  obtain ⟨⟨a,b⟩,hc⟩ := RawExact.QuotientPalette.optional_colour_realized T c
  obtain ⟨x,rfl⟩ := hπ a
  obtain ⟨y,rfl⟩ := hπ b
  exact ⟨S.colour (i := ()) (j := ()) x y,(quotientColourMap_at S T H π equivπ invariantT x y).trans hc⟩

theorem quotientColourMap_none : quotientColourMap S T π none = none := by
  obtain ⟨x⟩ := S.nonemptySort ()
  have he : S.colour (i := ()) (j := ()) x x = none := (S.colour_none_iff x x).mpr rfl
  rw [← he,quotientColourMap_at S T H π equivπ invariantT]
  exact (T.colour_none_iff _ _).mpr rfl

theorem quotientColourMap_not_injective (hn : ¬ Function.Injective π) :
    ¬ Function.Injective (quotientColourMap S T π) := by
  intro hinj
  apply hn
  intro x y hxy
  have hc : quotientColourMap S T π (S.colour (i := ()) (j := ()) x y) = quotientColourMap S T π none := by
    rw [quotientColourMap_at S T H π equivπ invariantT,
      quotientColourMap_none S T H π equivπ invariantT]
    exact (T.colour_none_iff _ _).mpr (congrArg (fun z => (⟨(),z⟩ : Sigma (fun _ : Unit => N))) hxy)
  have he := (S.colour_none_iff x y).mp (hinj hc)
  exact eq_of_heq (Sigma.mk.inj he).2

include hπ in
theorem quotient_diversity_palette_lt (hn : ¬ Function.Injective π) :
    letI := S.finiteAtom () ()
    letI := T.finiteAtom () ()
    Fintype.card (T.Atom () ()) < Fintype.card (S.Atom () ()) := by
  classical
  letI := S.finiteAtom () ()
  letI := T.finiteAtom () ()
  let f := quotientColourMap S T π
  have hf : Function.Surjective f :=
    quotientColourMap_surjective S T H π hπ equivπ invariantT
  let g := Function.surjInv hf
  have hg : Function.Injective g := Function.injective_surjInv hf
  have hng : ¬ Function.Surjective g := by
    intro hgs
    apply quotientColourMap_not_injective S T H π equivπ invariantT hn
    intro x y hxy
    obtain ⟨a,rfl⟩ := hgs x
    obtain ⟨b,rfl⟩ := hgs y
    have hab : a = b := by
      change f (g a) = f (g b) at hxy
      simpa only [g,Function.surjInv_eq] using hxy
    exact congrArg g hab
  have hcard := Fintype.card_lt_of_injective_not_surjective g hg hng
  simp only [Fintype.card_option] at hcard
  omega

end CCO.FinitePackets.Normalization
