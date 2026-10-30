import CCO.ParityHasse.Original.Equivalences
import CCO.RawOrbitals

/-! Full-language invariant equivalences are read on the very same
canonical pair carriers. Only actual pair orbitals are used here;
no higher tuple is transported through a binary isomorphism. -/
universe u v w t
namespace CCO.FullPhaseLift.Tower
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] {i : ι} [MulAction G (X i)]

/-- Invariance under the actual full automorphism action at one named sort. -/
abbrev InvariantEq := {E : Setoid (X i) //
  ∀ (g : G) x y, E x y → E (g • x) (g • y)}

/-- Complete canonical two-point names are exactly the full pair orbitals.
Full tuple homogeneity is not being inferred for the binary reduct. -/
theorem invariant_iff_pair_colours
    (hColour : S.ColourInvariant (G := G) (i := i) (j := i))
    (hPair : S.PairHomogeneous (G := G) (i := i) (j := i))
    (R : X i → X i → Prop) :
    (∀ (g : G) x y, R x y → R (g • x) (g • y)) ↔ ColourInvariant S i R := by
  constructor
  · intro hInv x y x' y' hcol
    obtain ⟨g,hgx,hgy⟩ := hPair x x' y y' hcol
    constructor
    · intro h
      simpa only [hgx,hgy] using hInv g x y h
    · intro h
      have hb := hInv g⁻¹ x' y' h
      rw [← hgx,← hgy] at hb
      simpa only [inv_smul_smul] using hb
  · intro hR g x y h
    exact (hR (g • x) (g • y) x y (hColour g x y)).mpr h

/-- The FULL invariant-equivalence poset, with no omitted higher-language
binary equivalence. The underlying equivalence relations are unchanged. -/
def invariantOrderIso
    (hColour : S.ColourInvariant (G := G) (i := i) (j := i))
    (hPair : S.PairHomogeneous (G := G) (i := i) (j := i)) :
    InvariantEq (X := X) (G := G) (i := i) ≃o ColourEq S i where
  toFun E := ⟨E.val,(invariant_iff_pair_colours S hColour hPair E.val).mp E.2⟩
  invFun E := ⟨E.val,(invariant_iff_pair_colours S hColour hPair E.val).mpr E.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Relative class sets are literally those of the same underlying
setoids, so this comparison also preserves finite relative indices. -/
def relativeClassEquiv
    (hColour : S.ColourInvariant (G := G) (i := i) (j := i))
    (hPair : S.PairHomogeneous (G := G) (i := i) (j := i))
    (E F : InvariantEq (X := X) (G := G) (i := i)) (a : X i) :
    RelativeClass E.val F.val a ≃
      RelativeClass (invariantOrderIso S hColour hPair E).val
        (invariantOrderIso S hColour hPair F).val a := Equiv.refl _

theorem relativeIndex_eq
    (hColour : S.ColourInvariant (G := G) (i := i) (j := i))
    (hPair : S.PairHomogeneous (G := G) (i := i) (j := i))
    (E F : InvariantEq (X := X) (G := G) (i := i)) (a : X i) :
    relativeIndex E.val F.val a =
      relativeIndex (invariantOrderIso S hColour hPair E).val
        (invariantOrderIso S hColour hPair F).val a := rfl

/-- A terminal canonical pair prefix has no proper finite-relative FULL
invariant cover. Actual relative classes and cover order are both retained. -/
theorem terminal_full_cover_infinite
    (hColour : S.ColourInvariant (G := G) (i := i) (j := i))
    (hPair : S.PairHomogeneous (G := G) (i := i) (j := i))
    (terminal : ∀ (E F : ColourEq S i), E ⋖ F → ∀ a : X i,
      Infinite (RelativeClass E.val F.val a))
    (E F : InvariantEq (X := X) (G := G) (i := i)) (hEF : E ⋖ F) (a : X i) :
    Infinite (RelativeClass E.val F.val a) := by
  let e := invariantOrderIso S hColour hPair
  have hmap : e E ⋖ e F := by
    refine ⟨e.strictMono hEF.lt,?_⟩
    intro C hEC hCF
    have hl : E < e.symm C := by simpa only [e.symm_apply_apply] using e.symm.strictMono hEC
    have hr : e.symm C < F := by simpa only [e.symm_apply_apply] using e.symm.strictMono hCF
    exact hEF.2 hl hr
  exact terminal (e E) (e F) hmap a

end CCO.FullPhaseLift.Tower
