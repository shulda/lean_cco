import CCO.ExactCRT.TypedPalette
import Mathlib.SetTheory.Cardinal.Finite

/-!
# B062 C106–C108: original diversity rank drops strictly on a real quotient

Use the ACTUAL typed quotient orbital source, not a renaming of unary
colour labels or a fictional quotient SAP. An original homogeneous
diversity colour can map to AT MOST one quotient optional colour;
each genuine quotient diversity orbital has an old diversity preimage.
If two distinct old real points collapse, their ORIGINAL diversity
colour becomes TRUE quotient equality. Thus there are strictly fewer
quotient diversity atoms. No rank of the larger marked expansion is
used, no old atom splits and logical diagonal never becomes diversity.

This statement applies to any surjective equivariant typed quotient,
not only the eventual exact original E-quotient. The E>Id assumption
supplies the collapsed-pair witness in the exact source instance.
-/

universe u v w z q t

namespace CCO.ExactEPGeometry

open CCO.RawExact.QuotientPalette

noncomputable section

/-- C106–C108 generic source-strength cardinal bound, with the exact
typed orbital palette already constructed by the pinned quotient
provider. No exactness, CCO, quotient SAP or group section is used. -/
theorem typedQuotientDiversityRank_strict_of_collapsed_pair
    {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X)
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    {K : Type z} [Fintype K] (Q : K → Type q)
    [∀ k : K, MulAction G (Q k)]
    (origin : K → ι) (pi : ∀ k, X (origin k) → Q k)
    (surj : ∀ k, Function.Surjective (pi k))
    (equiv : ∀ k (g : G) x, pi k (g • x) = g • pi k x)
    (k : K)
    (collapsed : ∃ x y : X (origin k), x ≠ y ∧ pi k x = pi k y) :
    let T := CCO.ExactCRT.TypedPalette.source Q S H origin pi surj equiv
    Nat.card (T.Atom k k) < Nat.card (S.Atom (origin k) (origin k)) := by
  classical
  let T := CCO.ExactCRT.TypedPalette.source Q S H origin pi surj equiv
  let rep : S.Atom (origin k) (origin k) →
      X (origin k) × X (origin k) :=
    fun a => colourRepresentatives S (some a)
  have hRep (a : S.Atom (origin k) (origin k)) :
      S.colour (rep a).1 (rep a).2 = some a :=
    colourRepresentatives_spec S (some a)
  let f : S.Atom (origin k) (origin k) → Option (T.Atom k k) :=
    fun a => T.colour (pi k (rep a).1) (pi k (rep a).2)
  have hColour (a : S.Atom (origin k) (origin k))
      (x y : X (origin k)) (hxy : S.colour x y = some a) :
      f a = T.colour (pi k x) (pi k y) := by
    obtain ⟨g,hgx,hgy⟩ :=
      (S.pair_homogeneous_of_homogeneous H)
        (rep a).1 x (rep a).2 y ((hRep a).trans hxy.symm)
    have hx : g • pi k (rep a).1 = pi k x := by
      calc
        g • pi k (rep a).1 = pi k (g • (rep a).1) :=
          (equiv k g (rep a).1).symm
        _ = pi k x := by rw [hgx]
    have hy : g • pi k (rep a).2 = pi k y := by
      calc
        g • pi k (rep a).2 = pi k (g • (rep a).2) :=
          (equiv k g (rep a).2).symm
        _ = pi k y := by rw [hgy]
    exact
      (CCO.ExactCRT.TypedPalette.source_colour_eq_iff_orbital
        Q S H origin pi surj equiv
        (pi k (rep a).1) (pi k (rep a).2) (pi k x) (pi k y)).mpr
        ⟨g,hx,hy⟩
  have hSurj : Function.Surjective f := by
    intro z
    cases z with
    | none =>
        obtain ⟨x,y,hne,hpi⟩ := collapsed
        cases hc : S.colour x y with
        | none =>
            have hxy : x = y := by
              have h := (S.colour_none_iff x y).mp hc
              simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h
            exact False.elim (hne hxy)
        | some a =>
            refine ⟨a,?_⟩
            have hn : T.colour (pi k x) (pi k y) = none := by
              apply (T.colour_none_iff (pi k x) (pi k y)).mpr
              exact congrArg
                (fun z : Q k => (⟨k,z⟩ : Sigma Q)) hpi
            exact (hColour a x y hc).trans hn
    | some b =>
        obtain ⟨p,r,hpr⟩ := T.realized b
        obtain ⟨x,hx⟩ := surj k p
        obtain ⟨y,hy⟩ := surj k r
        cases hc : S.colour x y with
        | none =>
            have hxy : x = y := by
              have h := (S.colour_none_iff x y).mp hc
              simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h
            have hn : T.colour (pi k x) (pi k y) = none := by
              apply (T.colour_none_iff (pi k x) (pi k y)).mpr
              rw [hxy]
            have hs : T.colour (pi k x) (pi k y) = some b := by
              simpa only [hx,hy] using hpr
            rw [hn] at hs
            cases hs
        | some a =>
            refine ⟨a,?_⟩
            calc
              f a = T.colour (pi k x) (pi k y) := hColour a x y hc
              _ = some b := by simpa only [hx,hy] using hpr
  letI : Fintype (S.Atom (origin k) (origin k)) :=
    S.finiteAtom (origin k) (origin k)
  letI : Fintype (T.Atom k k) := T.finiteAtom k k
  have hCard : Fintype.card (Option (T.Atom k k)) ≤
      Fintype.card (S.Atom (origin k) (origin k)) :=
    (by simpa only [Nat.card_eq_fintype_card] using
      (Nat.card_le_card_of_surjective f hSurj))
  have hOption : Fintype.card (Option (T.Atom k k)) =
      Fintype.card (T.Atom k k) + 1 := by simp
  have hStrict : Fintype.card (T.Atom k k) <
      Fintype.card (S.Atom (origin k) (origin k)) := by
    apply Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
    calc
      Fintype.card (T.Atom k k) + 1 =
          Fintype.card (Option (T.Atom k k)) := hOption.symm
      _ ≤ Fintype.card (S.Atom (origin k) (origin k)) := hCard
  simpa only [Nat.card_eq_fintype_card] using hStrict

end
end CCO.ExactEPGeometry
