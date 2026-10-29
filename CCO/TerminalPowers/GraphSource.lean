import CCO.TerminalPowers.FullSource
import CCO.RealClosure.Bounds.TerminalParity

/-! C01--C13: exact typed interfaces to the selected accepted B011 graph
providers. The relative parity interval is FULL and may lie below Top.
These results have no SAP, CCO, countability or exactness premise. -/
universe u v w t
namespace CCO.TerminalPowers
open ParityHasse.Original RealClosure.Bounds
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)] (H : HomogeneousSource S G)
variable {i : ι}

abbrev Connected (t : S.Atom i i) := connectivityColourEq S H t
abbrev EvenConnected (t : S.Atom i i) := evenColourEq S H t

include H in
/-- C01: every original real point has a distinct genuine t-neighbour. -/
theorem atom_neighbour (t : S.Atom i i) (x : X i) :
    ∃ y : X i, x ≠ y ∧ S.atomRel t x y := by
  obtain ⟨a,b,hab⟩ := S.realized t
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i a x
  have he : S.atomRel t x (g • b) := by
    simpa only [AtomicSource.atomRel,hg] using (S.colourInvariant_of_homogeneous H g a b).trans hab
  exact ⟨g • b,fun h => S.atomRel_ne he (congrArg (Sigma.mk i) h),he⟩

theorem even_le_connected (t : S.Atom i i) : EvenConnected S H t ≤ Connected S H t :=
  even_le_connectivity S H t

/-- C03: at most two actual even-walk classes in EVERY connectivity class,
without assuming absence of odd cycles or any NR2 condition. -/
theorem parity_class_finite_bound (t : S.Atom i i) (a : X i) :
    Finite (RelativeClass (EvenConnected S H t).val (Connected S H t).val a) ∧
      Nat.card (RelativeClass (EvenConnected S H t).val (Connected S H t).val a) ≤ 2 := by
  obtain ⟨b,_,hab⟩ := atom_neighbour S H t a
  let Y := EvenConnected S H t
  let C := Connected S H t
  let qa : RelativeClass Y.val C.val a := Quotient.mk _ ⟨a,C.val.refl a⟩
  let qb : RelativeClass Y.val C.val a := Quotient.mk _ ⟨b,1,(relPow_one _ _ _).mpr hab⟩
  let f : Bool → RelativeClass Y.val C.val a := fun z => if z then qb else qa
  have hf : Function.Surjective f := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rcases (connectivity_eq_even_union_odd S H t a x.val).mp x.property with he | ho
    · exact ⟨false,Quotient.sound he⟩
    · obtain ⟨n,hn,hax⟩ := ho
      have hxb : Y x.val b := by
        refine ⟨n+1,hn.add_one,?_⟩
        rw [relPow_add]
        exact ⟨a,relPow_symmetric (S.atomRel t)
          (fun x y h => (S.colour_swap x y t).mp h |>.trans (congrArg some (S.symmetricLoop t)))
          n a x.val hax,(relPow_one _ _ _).mpr hab⟩
      exact ⟨true,Quotient.sound (Y.val.symm hxb)⟩
  refine ⟨Finite.of_surjective f hf,?_⟩
  have hb : Nat.card Bool = 2 := Nat.card_eq_fintype_card
  simpa only [hb] using Nat.card_le_card_of_surjective f hf

/-- C05: absence of odd closed walks gives the actual relative index TWO,
even if connectivity is proper and neither endpoint is exact. -/
theorem bipartite_relative_index_two (t : S.Atom i i)
    (noOdd : ∀ x n, Odd n → ¬ relPow (S.atomRel t) n x x) (a : X i) :
    relativeIndex (EvenConnected S H t).val (Connected S H t).val a = 2 :=
  parity_seed_index_two S H t noOdd a

include H in
theorem nr2_odd_walk (nr2 : SortNR2 S i) (t : S.Atom i i) (x : X i) :
    ∃ p : (atomGraph S t).Walk x x, Odd p.length :=
  terminal_component_odd_walk S H nr2 t x

/-- D03/C11: literal original DIVERSITY names only, without real equality. -/
def connectivityPalette (t : S.Atom i i) : S.Menu i i :=
  {c | ∀ x y : X i, S.atomRel c x y → Connected S H t x y}

theorem atom_mem_connectivityPalette (t : S.Atom i i) : t ∈ connectivityPalette S H t :=
  fun _ _ h => ⟨1,(relPow_one _ _ _).mpr h⟩

theorem connectivityPalette_nonempty (t : S.Atom i i) : (connectivityPalette S H t).Nonempty :=
  ⟨t,atom_mem_connectivityPalette S H t⟩

theorem connectivityPalette_finite (t : S.Atom i i) : (connectivityPalette S H t).Finite := by
  let := S.finiteAtom i i
  exact Set.toFinite _

theorem connectivityPalette_representative (t : S.Atom i i)
    {c : S.Atom i i} (hc : c ∈ connectivityPalette S H t) :
    ∃ x y : X i, x ≠ y ∧ S.atomRel c x y ∧ Connected S H t x y := by
  obtain ⟨x,y,hxy⟩ := S.realized c
  exact ⟨x,y,fun he => S.atomRel_ne hxy (congrArg (Sigma.mk i) he),hxy,hc x y hxy⟩

/-- Selected B011 C26 supplies ONE positive threshold before varying either
the actual real endpoint pair or the requested length. Diagonals stay RAW. -/
theorem uniform_represented_threshold (nr2 : SortNR2 S i) (t : S.Atom i i) :
    ∃ N : Nat, 0 < N ∧ ∀ n, N ≤ n → ∀ x y : X i,
      Connected S H t x y → relPow (S.atomRel t) n x y := by
  obtain ⟨N,hN,hpow⟩ := terminal_uniform_atomic_powers S H nr2 t
  refine ⟨N,hN,?_⟩
  intro n hn x y hxy
  have he := congrFun (congrFun (hpow n hn) x) y
  rw [atomWord_relation] at he
  exact he.symm ▸ hxy

/-- Fixed actual diversity representatives and ONE positive finite-palette
threshold are chosen BEFORE a later walk length or endpoint pair is varied.
The accepted C26 uniformization also covers RAW diagonals, unused here. -/
theorem finite_literal_representative_threshold (nr2 : SortNR2 S i) (t : S.Atom i i) :
    ∃ N : Nat, 0 < N ∧
      ∃ representative : {c : S.Atom i i // c ∈ connectivityPalette S H t} → X i × X i,
        ∀ c, (representative c).1 ≠ (representative c).2 ∧
          S.atomRel c.val (representative c).1 (representative c).2 ∧
          ∀ n, N ≤ n → relPow (S.atomRel t) n (representative c).1 (representative c).2 := by
  classical
  obtain ⟨N,hN,hwalk⟩ := uniform_represented_threshold S H nr2 t
  choose x y hcol using (fun c : {c : S.Atom i i // c ∈ connectivityPalette S H t} => S.realized c.val)
  refine ⟨N,hN,(fun c => (x c,y c)),?_⟩
  intro c
  exact ⟨fun he => S.atomRel_ne (hcol c) (congrArg (Sigma.mk i) he),hcol c,
    fun n hn => hwalk n hn _ _ (c.property _ _ (hcol c))⟩

end CCO.TerminalPowers
