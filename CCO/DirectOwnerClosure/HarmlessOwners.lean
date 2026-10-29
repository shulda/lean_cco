import CCO.DirectOwnerClosure.DirectHull

/-! C08--C13: the specialized good-real-representative proof is written
locally. Actual imaginary owners, rather than these proof choices, are named.
There is no countability, exactness, normalization, or B022 theorem input. -/
universe v w t
namespace CCO.DirectOwnerClosure
open ParityHasse.Original RealHull.Geometry RealHull.Canonical
open FinitePackets.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

theorem real_acl_subset_ownerClosure (E : ColourEq S ()) (B : Finset (Owner S E))
    (A : Finset M) : algebraicClosure (FullAut S) A ⊆ ownerClosure S E B A := by
  intro x hx
  apply hx.subset
  rintro y ⟨g,hg,_,hgy⟩
  exact ⟨g,hg,hgy⟩

/-- D05 includes the genuine p;p relation, whose endpoints may coincide. -/
def BadColour (E : ColourEq S ()) (p : Atom S) : Prop :=
  ∀ u z : M, E u z → (∃ y : M, col S u y = some p ∧ col S y z = some p) →
    packet S H u z

theorem bad_neighbours_finite (E : ColourEq S ()) (p : Atom S)
    (hp : BadColour S H E p) (x c : M) :
    {b : M | E c b ∧ col S x b = some p}.Finite := by
  let N : Set M := {b | E c b ∧ col S x b = some p}
  by_cases hn : N.Nonempty
  · obtain ⟨b,hb⟩ := hn
    apply (packet_class_finite S H b).subset
    intro z hz
    exact hp b z (E.val.trans (E.val.symm hb.1) hz.1)
      ⟨x,(col_symm S b x).trans hb.2,hz.2⟩
  · change N.Finite
    rw [Set.not_nonempty_iff_eq_empty.mp hn]
    exact Set.finite_empty

theorem good_colour_contains (E : ColourEq S ()) (hE : MinimalInfiniteCut S E)
    (p : Atom S) (hp : ¬ BadColour S H E p) : E ≤ connectivity S p := by
  have hnot : ¬ FiniteIndex S ⊥ (E ⊓ connectivity S p) := by
    intro hf
    have hle := sigma_greatest S H bot_le hf
    apply hp
    intro u z huz hsq
    obtain ⟨y,huy,hyz⟩ := hsq
    exact hle ⟨huz,(connectivity S p).val.trans
      (atom_mem_connectivity S p huy) (atom_mem_connectivity S p hyz)⟩
  by_contra hn
  have hstrict : E ⊓ connectivity S p < E :=
    lt_of_le_of_ne inf_le_left (fun he => hn (he ▸ inf_le_right))
  exact hnot (hE.2 _ hstrict)

include H in
/-- C09--C11: avoid every bad colour fibre and x itself in the actual
infinite owner class. Equality can therefore never serve as a spoke. -/
theorem exists_good_representative (E : ColourEq S ()) (hE : MinimalInfiniteCut S E)
    (q : Owner S E) (x : M) :
    ∃ b : M, owner S E b = q ∧ b ≠ x ∧
      ∃ p : Atom S, col S x b = some p ∧ E ≤ connectivity S p := by
  classical
  let := S.finiteAtom () ()
  let bad : Atom S → Set M := fun p =>
    if BadColour S H E p then {b | E q.out b ∧ col S x b = some p} else ∅
  have hf : ∀ p, (bad p).Finite := by
    intro p
    unfold bad
    split_ifs with hp
    · exact bad_neighbours_finite S H E p hp x q.out
    · exact Set.finite_empty
  have hforbid : ({x} ∪ ⋃ p : Atom S, bad p).Finite :=
    (Set.finite_singleton x).union (Set.finite_iUnion hf)
  have hclass : {b : M | E q.out b}.Infinite :=
    Set.infinite_coe_iff.mp (cut_actual_classes_infinite S H hE q.out)
  obtain ⟨b,hb,hbout⟩ := hclass.sdiff hforbid |>.nonempty
  have hne : b ≠ x := by
    intro he
    exact hbout (Or.inl (Set.mem_singleton_iff.mpr he))
  obtain ⟨p,hp⟩ := col_some_of_ne S (Ne.symm hne)
  have hgood : ¬ BadColour S H E p := by
    intro hbad
    apply hbout
    right
    apply Set.mem_iUnion.mpr
    refine ⟨p,?_⟩
    change b ∈ (if BadColour S H E p then {b | E q.out b ∧ col S x b = some p} else ∅)
    rw [ite_eq_left hbad]
    exact ⟨hb,hp⟩
  exact ⟨b,(Quotient.sound (E.val.symm hb)).trans (Quotient.out_eq q),hne,
    p,hp,good_colour_contains S H E hE p hgood⟩

/-- Original full automorphisms fixing auxiliary real representatives form
a SUBGROUP of the individually named actual-owner stabilizer. -/
theorem ownerClosure_subset_representatives [DecidableEq M]
    (E : ColourEq S ()) (B : Finset (Owner S E)) (A : Finset M)
    (b : ↥B → M) (hb : ∀ i, owner S E (b i) = i.val) :
    ownerClosure S E B A ⊆ algebraicClosure (FullAut S) (A ∪ Finset.univ.image b) := by
  intro x hx
  apply hx.subset
  rintro y ⟨g,hg,hgy⟩
  refine ⟨g,fun a ha => hg a (Finset.mem_union_left _ ha),?_,hgy⟩
  intro q hq
  let i : ↥B := ⟨q,hq⟩
  apply (fixesOwner_iff S E q g (b i) (hb i)).mpr
  have hfix : g.val (b i) = b i := hg (b i) (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  rw [hfix]
  exact hb i

/-- C12--C13: the SAME E survives all original real spokes and all chosen
representative spokes. A finite named-owner orbit would force a finite hull. -/
theorem named_owner_acl [DecidableEq M] [Infinite M]
    (cco : SemanticCCO.{0,v,0,w} S) {E : ColourEq S ()} (hE : UniqueDirection S E)
    (B : Finset (Owner S E)) (A : Finset M) :
    ownerClosure S E B A = packetHull S H A := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxF
    have hxA := outside_packet_not_parameter S H A x hxF
    have hg : ∀ i : ↥B, ∃ b : M, owner S E b = i.val ∧ b ≠ x ∧
        ∃ p : Atom S, col S x b = some p ∧ E ≤ connectivity S p :=
      fun i => exists_good_representative S H E hE.1 i.val x
    choose b hb hbx p hpb hEp using hg
    let C : Finset M := A ∪ Finset.univ.image b
    have hxC : x ∉ C := by
      intro hmem
      rcases Finset.mem_union.mp hmem with ha | hbmem
      · exact hxA ha
      · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hbmem
        exact hbx i hi
    have halg : x ∈ algebraicClosure (FullAut S) C :=
      ownerClosure_subset_representatives S E B A b hb hx
    apply outside_acl_of_direction_spokes S H cco hE.1 C x hxC ?_ halg
    intro a
    rcases Finset.mem_union.mp a.property with ha | hbmem
    · let aA : ↥A := ⟨a.val,ha⟩
      have he : actualSpokes S C x hxC a = actualSpokes S A x hxA aA :=
        Option.some.inj ((actualSpokes_colour S C x hxC a).symm.trans
          (actualSpokes_colour S A x hxA aA))
      rw [he]
      exact outside_spoke_contains_direction S H hE A x hxF aA
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hbmem
      have he : actualSpokes S C x hxC a = p i :=
        Option.some.inj ((actualSpokes_colour S C x hxC a).symm.trans
          (by rw [← hi]; exact hpb i))
      rw [he]
      exact hEp i
  · intro x hx
    exact real_acl_subset_ownerClosure S E B A (packetHull_subset_real_acl S H A hx)

include H in
theorem named_owner_acl_eq_real [DecidableEq M] [Infinite M]
    (cco : SemanticCCO.{0,v,0,w} S) {E : ColourEq S ()} (hE : UniqueDirection S E)
    (B : Finset (Owner S E)) (A : Finset M) :
    ownerClosure S E B A = algebraicClosure (FullAut S) A := by
  rw [named_owner_acl S H cco hE B A,direct_real_acl S H cco hE A]

end CCO.DirectOwnerClosure
