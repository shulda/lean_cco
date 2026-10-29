import CCO.ProfileHelly.Paths

/-! C13--C15: arbitrary shared internal vertices can be split in either
order. Both smaller comparisons strictly decrease the actual shared-INTERNAL
vertex count; endpoints are allowed to have already recorded edges. -/
universe u v z
namespace CCO.ProfileHelly.Network
variable {ι : Type u} {T : Table.{u,v} ι} {V : Type z} {sort : V → ι}
variable (D : Network T sort) [DecidableEq V]
open SimpleGraph

theorem prefix_internal_subset {x y a : V} (p : D.graph.Path x y)
    (ha : a ∈ D.internal p.val) :
    D.internal (D.prefixPath p ((D.mem_internal _).mp ha).1).val ⊆
      (D.internal p.val).erase a := by
  classical
  rcases (D.mem_internal _).mp ha with ⟨hap,hax,hay⟩
  intro b hb
  rcases (D.mem_internal _).mp hb with ⟨hbp,hbx,hba⟩
  change b ∈ (p.val.takeUntil a hap).support at hbp
  have hby : b ≠ y := by
    intro he
    exact Walk.endpoint_notMem_support_takeUntil p.property hap hay.symm (he ▸ hbp)
  exact Finset.mem_erase.mpr ⟨hba,(D.mem_internal _).mpr
    ⟨p.val.support_takeUntil_subset_support hap hbp,hbx,hby⟩⟩

theorem suffix_internal_subset {x y a : V} (p : D.graph.Path x y)
    (ha : a ∈ D.internal p.val) :
    D.internal (D.suffixPath p ((D.mem_internal _).mp ha).1).val ⊆
      (D.internal p.val).erase a := by
  classical
  rcases (D.mem_internal _).mp ha with ⟨hap,hax,hay⟩
  intro b hb
  rcases (D.mem_internal _).mp hb with ⟨hbp,hba,hby⟩
  change b ∈ (p.val.dropUntil a hap).support at hbp
  have hj : ((p.val.takeUntil a hap).append (p.val.dropUntil a hap)).IsPath := by
    simpa only [Walk.take_spec] using p.property
  have hbx : b ≠ x := by
    have hn := hj.ne_of_mem_support_of_append hba
      (p.val.takeUntil a hap).start_mem_support hbp
    exact hn.symm
  exact Finset.mem_erase.mpr ⟨hba,(D.mem_internal _).mpr
    ⟨p.val.support_dropUntil_subset_support hap hbp,hbx,hby⟩⟩

theorem shared_prefix_internal_lt {x y a : V} (p q : D.graph.Path x y)
    (hp : a ∈ D.internal p.val) (hq : a ∈ D.internal q.val) :
    (D.internal (D.prefixPath p ((D.mem_internal _).mp hp).1).val ∩
      D.internal (D.prefixPath q ((D.mem_internal _).mp hq).1).val).card <
      (D.internal p.val ∩ D.internal q.val).card := by
  classical
  have hs : D.internal (D.prefixPath p ((D.mem_internal _).mp hp).1).val ∩
      D.internal (D.prefixPath q ((D.mem_internal _).mp hq).1).val ⊆
      (D.internal p.val ∩ D.internal q.val).erase a := by
    intro b hb
    obtain ⟨hbp,hbq⟩ := Finset.mem_inter.mp hb
    obtain ⟨hba,hbp⟩ := Finset.mem_erase.mp (D.prefix_internal_subset p hp hbp)
    obtain ⟨_,hbq⟩ := Finset.mem_erase.mp (D.prefix_internal_subset q hq hbq)
    exact Finset.mem_erase.mpr ⟨hba,Finset.mem_inter.mpr ⟨hbp,hbq⟩⟩
  exact (Finset.card_le_card hs).trans_lt (Finset.card_erase_lt_of_mem (Finset.mem_inter.mpr ⟨hp,hq⟩))

theorem shared_suffix_internal_lt {x y a : V} (p q : D.graph.Path x y)
    (hp : a ∈ D.internal p.val) (hq : a ∈ D.internal q.val) :
    (D.internal (D.suffixPath p ((D.mem_internal _).mp hp).1).val ∩
      D.internal (D.suffixPath q ((D.mem_internal _).mp hq).1).val).card <
      (D.internal p.val ∩ D.internal q.val).card := by
  classical
  have hs : D.internal (D.suffixPath p ((D.mem_internal _).mp hp).1).val ∩
      D.internal (D.suffixPath q ((D.mem_internal _).mp hq).1).val ⊆
      (D.internal p.val ∩ D.internal q.val).erase a := by
    intro b hb
    obtain ⟨hbp,hbq⟩ := Finset.mem_inter.mp hb
    obtain ⟨hba,hbp⟩ := Finset.mem_erase.mp (D.suffix_internal_subset p hp hbp)
    obtain ⟨_,hbq⟩ := Finset.mem_erase.mp (D.suffix_internal_subset q hq hbq)
    exact Finset.mem_erase.mpr ⟨hba,Finset.mem_inter.mpr ⟨hbp,hbq⟩⟩
  exact (Finset.card_le_card hs).trans_lt (Finset.card_erase_lt_of_mem (Finset.mem_inter.mpr ⟨hp,hq⟩))

/-- C15, uniformly over ALL distinct endpoints, recorded or unrecorded.
No order-compatibility of common vertices is assumed. -/
theorem path_profiles_intersect (laws : TableLaws T) (alg : D.Algebraic)
    (x y : V) (hxy : x ≠ y) (p q : D.graph.Path x y) :
    (D.pathProfile hxy p ∩ D.pathProfile hxy q).Nonempty := by
  classical
  have main : ∀ n : Nat, ∀ (x y : V) (hxy : x ≠ y) (p q : D.graph.Path x y),
      (D.internal p.val ∩ D.internal q.val).card = n →
        (D.pathProfile hxy p ∩ D.pathProfile hxy q).Nonempty := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x y hxy p q hn
      by_cases hpq : p = q
      · subst q
        obtain ⟨c,hc⟩ := D.pathProfile_nonempty laws hxy p
        exact ⟨c,hc,hc⟩
      by_cases hd : Disjoint (D.internal p.val) (D.internal q.val)
      · exact alg x y hxy p q hd hpq
      obtain ⟨a,hap,haq⟩ := Finset.not_disjoint_iff.mp hd
      have hxa : x ≠ a := ((D.mem_internal _).mp hap).2.1.symm
      have hay : a ≠ y := ((D.mem_internal _).mp hap).2.2
      let pL := D.prefixPath p ((D.mem_internal _).mp hap).1
      let qL := D.prefixPath q ((D.mem_internal _).mp haq).1
      let pR := D.suffixPath p ((D.mem_internal _).mp hap).1
      let qR := D.suffixPath q ((D.mem_internal _).mp haq).1
      have hl : (D.internal pL.val ∩ D.internal qL.val).card < n :=
        hn ▸ D.shared_prefix_internal_lt p q hap haq
      have hr : (D.internal pR.val ∩ D.internal qR.val).card < n :=
        hn ▸ D.shared_suffix_internal_lt p q hap haq
      obtain ⟨b,hbp,hbq⟩ := ih _ hl x a hxa pL qL rfl
      obtain ⟨c,hcp,hcq⟩ := ih _ hr a y hay pR qR rfl
      obtain ⟨d,hd⟩ := laws.total b c
      have hp := D.prefix_suffix_profile laws hxy hxa hay p ((D.mem_internal _).mp hap).1
      have hq := D.prefix_suffix_profile laws hxy hxa hay q ((D.mem_internal _).mp haq).1
      refine ⟨d,?_,?_⟩
      · rw [hp]
        exact T.product_mono (Set.singleton_subset_iff.mpr hbp) (Set.singleton_subset_iff.mpr hcp) hd
      · rw [hq]
        exact T.product_mono (Set.singleton_subset_iff.mpr hbq) (Set.singleton_subset_iff.mpr hcq) hd
  exact main _ x y hxy p q rfl

end CCO.ProfileHelly.Network
