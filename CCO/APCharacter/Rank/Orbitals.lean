import CCO.APCharacter.Rank.Source

/-! Whole-expanded homogeneity identifies the actual pair orbitals with the
old names occurring in a fixed child.  No homogeneity of child reducts is
substituted for this hypothesis. -/
universe u v w t z
namespace CCO.APCharacter.Rank
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable (β : ι → Type t) (tag : ∀ i, X i → β i)

theorem colour_eq_iff {c d : Child β}
    (x x' : Point β tag c) (y y' : Point β tag d) :
    colour S β tag x y = colour S β tag x' y' ↔
      S.colour x.val y.val = S.colour x'.val y'.val := by
  constructor
  · intro h
    simpa only [colour_map] using congrArg (Option.map Subtype.val) h
  · intro h
    unfold colour
    split <;> split <;> simp_all [Subtype.ext_iff]

variable [∀ i, Fintype (β i)] (inhabited : ∀ c, Nonempty (Point β tag c))
variable {G : Type z} [Group G] [∀ c : Child β, MulAction G (Point β tag c)]

/-- This is actual orbit recognition under the WHOLE expanded source action,
for every fixed ordered pair of child sorts. -/
theorem same_old_colour_iff_orbit
    (H : HomogeneousSource (source S β tag inhabited) G) {c d : Child β}
    (x x' : Point β tag c) (y y' : Point β tag d) :
    S.colour x.val y.val = S.colour x'.val y'.val ↔
      ∃ g : G, g • x = x' ∧ g • y = y' := by
  constructor
  · intro h
    exact (source S β tag inhabited).pair_homogeneous_of_homogeneous H x x' y y'
      ((colour_eq_iff S β tag x x' y y').mpr h)
  · rintro ⟨g,hx,hy⟩
    apply (colour_eq_iff S β tag x x' y y').mp
    have h := (source S β tag inhabited).colourInvariant_of_homogeneous H g x y
    change colour S β tag (g • x) (g • y) = colour S β tag x y at h
    simpa only [hx,hy] using h.symm

/-- Every remaining named child colour is one complete actual orbital,
including for the full automorphism group when that is the source action. -/
theorem child_colour_is_actual_orbital
    (H : HomogeneousSource (source S β tag inhabited) G) {c : Child β}
    (a : Colour S β tag c c) :
    ∃ x y : Point β tag c,
      (source S β tag inhabited).atomRel a x y ∧
      (source S β tag inhabited).atomRel a = GroupActions.orbital (G := G) x y :=
  (source S β tag inhabited).diversity_atom_is_orbital_of_homogeneous H a

end CCO.APCharacter.Rank
