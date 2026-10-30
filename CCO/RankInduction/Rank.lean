import CCO.RankInduction.Basis
import CCO.FinitePackets.Normalization.PaletteDescent

/-! Actual orbital counting. Exactness supplies the standing quotient
source separately; it is not needed for the strict counting theorem. -/

universe v w q r t
namespace CCO.RankInduction
open FinitePackets.Normalization RawExact ExactCRT
noncomputable section

variable {M : Type v} {N : Type q}
variable (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (T : AtomicSource.{0,q,r} Unit (fun _ => N))
variable {G : Type t} [Group G] [MulAction G M] [MulAction G N]
variable (H : HomogeneousSource S G)
variable (π : M → N) (onto : Function.Surjective π)
variable (equivariant : ∀ (g : G) x, π (g • x) = g • π x)
variable (invariant : ∀ (g : G) x y,
  T.colour (i := ()) (j := ()) (g • x) (g • y) = T.colour x y)

include H onto equivariant invariant in
/-- Every old equality-inclusive orbital has one actual quotient colour,
and every quotient diversity colour is reached. -/
theorem actual_orbital_colour_surjective :
    Function.Surjective (quotientColourMap S T π) :=
  quotientColourMap_surjective S T H π onto equivariant invariant

include H onto equivariant invariant in
/-- A noninjective equivariant surjection consumes a genuine old diversity
orbital in equality. No CCO, exactness or full-group surjectivity is used. -/
theorem actual_quotient_rank_lt (proper : ¬ Function.Injective π) :
    rank T < rank S := by
  let _ := S.finiteAtom () ()
  let _ := T.finiteAtom () ()
  simpa only [rank, Nat.card_eq_fintype_card] using
    quotient_diversity_palette_lt S T H π onto equivariant invariant proper

include H onto equivariant invariant in
/-- For an injective quotient the complete ORIGINAL-group orbital names
are unchanged. Merely using an arbitrary coarser invariant colouring
would not prove this identity-boundary statement. -/
theorem actual_quotient_rank_eq (injective : Function.Injective π)
    (complete : ∀ x y x' y' : N,
      T.colour (i := ()) (j := ()) x y = T.colour x' y' ↔
        GroupActions.orbital (G := G) x y x' y') :
    rank T = rank S := by
  classical
  let _ := S.finiteAtom () ()
  let _ := T.finiteAtom () ()
  let f := quotientColourMap S T π
  have hf : Function.Injective f := by
    intro a b hab
    let p := QuotientPalette.colourRepresentatives S a
    let z := QuotientPalette.colourRepresentatives S b
    have hc : T.colour (i := ()) (j := ()) (π p.1) (π p.2) =
        T.colour (π z.1) (π z.2) := hab
    obtain ⟨g, hg₁, hg₂⟩ := (complete _ _ _ _).mp hc
    have hx : g • p.1 = z.1 := injective ((equivariant g p.1).trans hg₁)
    have hy : g • p.2 = z.2 := injective ((equivariant g p.2).trans hg₂)
    have he := S.colourInvariant_of_homogeneous H (i := ()) (j := ()) g p.1 p.2
    rw [hx, hy] at he
    exact (QuotientPalette.colourRepresentatives_spec S a).symm.trans
      (he.symm.trans (QuotientPalette.colourRepresentatives_spec S b))
  have he := Fintype.card_congr (Equiv.ofBijective f
    ⟨hf, actual_orbital_colour_surjective S T H π onto equivariant invariant⟩)
  simp only [Fintype.card_option] at he
  simp only [rank, Nat.card_eq_fintype_card]
  omega

omit T H π onto equivariant invariant in
theorem rank_zero_subsingleton (zero : rank S = 0) : Subsingleton M := by
  classical
  let _ := S.finiteAtom () ()
  have hz : Fintype.card (S.Atom () ()) = 0 := by
    simpa only [rank, Nat.card_eq_fintype_card] using zero
  constructor
  intro x y
  cases hc : S.colour (i := ()) (j := ()) x y with
  | none =>
    exact eq_of_heq (Sigma.mk.inj ((S.colour_none_iff x y).mp hc)).2
  | some a =>
    have hp : 0 < Fintype.card (S.Atom () ()) := Fintype.card_pos_iff.mpr ⟨a⟩
    omega

omit T H π onto equivariant invariant in
theorem rank_eq_zero_of_subsingleton [Subsingleton M] : rank S = 0 := by
  classical
  let _ := S.finiteAtom () ()
  have : IsEmpty (S.Atom () ()) := ⟨by
    intro a
    obtain ⟨x, y, hc⟩ := S.realized a
    have hn : S.colour (i := ()) (j := ()) x y = none :=
      (S.colour_none_iff x y).mpr (congrArg (fun x => (⟨(), x⟩ : Sigma (fun _ : Unit => M)))
        (Subsingleton.elim x y))
    rw [hn] at hc
    cases hc⟩
  simp only [rank, Nat.card_eq_fintype_card, Fintype.card_eq_zero]

section ExactQuotients
variable (cco : SemanticCCO.{0,v,v,w} S)
variable (E : ExactEq S H cco ())
local instance rankExactQuotientInvariant : CanonicalQuotients.Invariant G E.val :=
  Owners.Product.exactInvariant S H cco E

/-- The actual standing-source quotient used in the recursion has strictly
smaller diversity rank for EVERY nonidentity exact kernel, including Top. -/
theorem exact_quotient_rank_lt (proper : E ≠ ⊥) :
    rank (Owners.Master.quotientSource S H cco E) < rank S := by
  apply actual_quotient_rank_lt S (Owners.Master.quotientSource S H cco E) H
    (Quotient.mk'' : M → Quotient E.val) Quotient.mk''_surjective (fun _ _ => rfl)
    (fun g x y => (Owners.Master.quotientSource_colour_orbital S H cco E
      x y (g • x) (g • y)).mpr ⟨g, rfl, rfl⟩ |>.symm)
  intro hinj
  apply proper
  apply Subtype.ext
  apply Setoid.ext
  intro x y
  change E.val x y ↔ x = y
  exact ⟨fun h => hinj (Quotient.sound h), fun h => h ▸ E.val.refl x⟩

/-- Id is an isomorphic boundary, never a strict recursion call. -/
theorem identity_quotient_rank :
    rank (Owners.Master.quotientSource S H cco (⊥ : ExactEq S H cco ())) = rank S := by
  let E : ExactEq S H cco () := ⊥
  let _ : CanonicalQuotients.Invariant G E.val := Owners.Product.exactInvariant S H cco E
  apply actual_quotient_rank_eq S (Owners.Master.quotientSource S H cco E) H
    (Quotient.mk'' : M → Quotient E.val) Quotient.mk''_surjective (fun _ _ => rfl)
    (fun g x y => (Owners.Master.quotientSource_colour_orbital S H cco E
      x y (g • x) (g • y)).mpr ⟨g, rfl, rfl⟩ |>.symm)
  · intro x y h
    exact Quotient.exact h
  · exact Owners.Master.quotientSource_colour_orbital S H cco E

end ExactQuotients
end
end CCO.RankInduction
