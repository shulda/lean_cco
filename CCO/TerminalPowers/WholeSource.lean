import CCO.TerminalPowers.Saturation

/-! FULL whole-original-source NR2, allowing arbitrary invariant setoids
on the chosen named sort. No automorphism of its induced reduct is used. -/
universe u v w
namespace CCO.TerminalPowers
open ParityHasse.Original RealClosure.Bounds
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def FullInvariant (i : ι) (E : Setoid (X i)) : Prop :=
  ∀ (g : FullAut S) x y, E (g • x) (g • y) ↔ E x y

def FullSortNR2 (i : ι) : Prop :=
  ∀ E F : Setoid (X i), FullInvariant S i E → FullInvariant S i F → E ≤ F →
    ∀ x : X i, relativeIndex E F x ≠ 2

theorem fullInvariant_of_colour (i : ι) (E : ColourEq S i) : FullInvariant S i E.val :=
  fun g x y => E.property _ _ _ _ (fullAut_colour S g i i x y)

theorem sortNR2_of_full (i : ι) (nr2 : FullSortNR2 S i) : SortNR2 S i :=
  fun E F hEF x => nr2 E.val F.val (fullInvariant_of_colour S i E)
    (fullInvariant_of_colour S i F) hEF x

theorem colourInvariant_of_full (H : HomogeneousSource S (FullAut S)) (i : ι)
    (E : Setoid (X i)) (hE : FullInvariant S i E) : ColourInvariant S i E := by
  intro x y x' y' hc
  obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y' hc
  have he := hE g x y
  rw [hgx,hgy] at he
  exact he.symm

theorem fullSortNR2_iff (H : HomogeneousSource S (FullAut S)) (i : ι) :
    FullSortNR2 S i ↔ SortNR2 S i := by
  constructor
  · exact sortNR2_of_full S i
  · intro h E F hE hF hEF x
    exact h ⟨E,colourInvariant_of_full S H i E hE⟩
      ⟨F,colourInvariant_of_full S H i F hF⟩ hEF x

/-- The exact scoped source theorem uses FULL Aut of the WHOLE original
typed source, and NR2 on ALL its invariant equivalences of the fixed sort. -/
theorem terminal_pure_power_full (H : HomogeneousSource S (FullAut S)) (sap : AgeSAP S)
    (i : ι) (nr2 : FullSortNR2 S i) (t : S.Atom i i) :
    ∃ N : ℕ+, ∀ n : ℕ+, N.val ≤ n.val → purePower S t n = connectivityPalette S H t :=
  terminal_pure_power S H sap (sortNR2_of_full S i nr2) t

/-- The universal diversity-atom assertion is vacuous on an empty palette. -/
theorem empty_diversity_vacuous (i : ι) [IsEmpty (S.Atom i i)]
    (P : S.Atom i i → Prop) : ∀ t, P t := fun t => isEmptyElim t

end CCO.TerminalPowers
