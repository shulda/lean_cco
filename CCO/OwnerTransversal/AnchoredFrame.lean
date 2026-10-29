import CCO.OwnerTransversal.AnchoredNetwork
import CCO.RawExact.QuotientExpansionReadout

/-! Canonical private-word construction for a finite protected frame.
An already recorded atom on an owner link is retained: compatibility
forces that whole atom below E, so a second parallel word is redundant.
Every missing owner link receives its own private reachable-E path. -/
universe v w t
namespace CCO.OwnerTransversal
open ParityHasse.Original RawExact RawExact.QuotientExpansion

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

structure RawRecords (V : Type) where
  edge : V → V → Option (S.Atom () ())
  diagonal : ∀ x, edge x x = none
  symmetric : ∀ x y, edge x y = edge y x

def RawRecords.Hom {V : Type} (D : RawRecords S V) (f : V → M) : Prop :=
  ∀ x y a, D.edge x y = some a → S.colour (i := ()) (j := ()) (f x) (f y) = some a

def RawRecords.CompleteOn {V : Type} (D : RawRecords S V) (T : Finset V) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ∃ a, D.edge x y = some a

theorem saturated_atom_same_owner (E : ColourEq S ()) (a : S.Atom () ())
    {r s : M} (hrs : E r s) (h : ownerSaturate E.val (S.atomRel a) r s) :
    ∀ x y, S.atomRel a x y → E x y := by
  obtain ⟨z,⟨u,hru,huz⟩,hzs⟩ := h
  have he : E u z := E.val.trans (E.val.symm hru) (E.val.trans hrs (E.val.symm hzs))
  intro x y hxy
  exact (E.property u z x y (huz.trans hxy.symm)).mp he

variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

include H in
/-- C04: one raw homomorphism agrees on a complete protected frame after
one finite realignment.  Completeness supplies all ordered pair colours. -/
theorem align_complete_frame {n : Nat} (D : RawRecords S (Fin n))
    (T : Finset (Fin n)) (complete : RawRecords.CompleteOn S D T)
    (f j : Fin n → M) (hf : RawRecords.Hom S D f) (hj : RawRecords.Hom S D j) :
    ∃ g : G, ∀ x ∈ T, g • f x = j x := by
  classical
  let src : ULift.{v} ↥T → Sigma (fun _ : Unit => M) := fun x => ⟨(),f x.down.val⟩
  let dst : ULift.{v} ↥T → Sigma (fun _ : Unit => M) := fun x => ⟨(),j x.down.val⟩
  have hp : ∀ x y, taggedColour S (src x) (src y) = taggedColour S (dst x) (dst y) := by
    intro x y
    change (⟨(),(),S.colour (i := ()) (j := ()) (f x.down.val) (f y.down.val)⟩ :
      Σ i : Unit, Σ j : Unit, Option (S.Atom i j)) =
      ⟨(),(),S.colour (i := ()) (j := ()) (j x.down.val) (j y.down.val)⟩
    by_cases hxy : x.down.val = y.down.val
    · rw [hxy,(S.colour_none_iff _ _).mpr rfl,(S.colour_none_iff _ _).mpr rfl]
    · obtain ⟨a,ha⟩ := complete _ x.down.property _ y.down.property hxy
      rw [hf _ _ a ha,hj _ _ a ha]
  obtain ⟨g,hg⟩ := H.extends_finite_diagram src dst hp
  refine ⟨g,?_⟩
  intro x hx
  have hh := hg ⟨⟨x,hx⟩⟩
  change (⟨(),g • f x⟩ : Sigma (fun _ : Unit => M)) = ⟨(),j x⟩ at hh
  simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hh

section Construction
variable {n : Nat} (D : RawRecords S (Fin n)) (rep : Fin n → Fin n)

def frameLink (e : Edge n) : Prop :=
  rep (left e) = right e ∨ rep (right e) = left e

noncomputable def frameWords (word : RawWord S () ()) : Edge n → Option (RawWord S () ()) := by
  classical
  exact fun e => match D.edge (left e) (right e) with
    | some a => some (.atom a (.nil ()))
    | none => if frameLink rep e then some word else none

theorem frameWords_atom (word : RawWord S () ()) (e : Edge n) (a : S.Atom () ())
    (h : D.edge (left e) (right e) = some a) :
    frameWords S D rep word e = some (.atom a (.nil ())) := by
  simp only [frameWords,h]

theorem frameWords_nonempty (word : RawWord S () ()) (E : ColourEq S ())
    (hword : RawWord.relation S word = E.val.r) :
    ∀ e, frameWords S D rep word e ≠ none →
      TRel.Nonempty (RawWord.relation S (networkWord S (frameWords S D rep word) e)) := by
  classical
  intro e he
  cases hc : D.edge (left e) (right e) with
  | some a =>
    obtain ⟨x,y,hxy⟩ := S.realized a
    refine ⟨x,y,?_⟩
    simpa only [networkWord,frameWords,hc,Option.getD_some,direct_word_is_atom,AtomicSource.atomRel] using hxy
  | none =>
    by_cases hl : frameLink rep e
    · obtain ⟨x⟩ := S.nonemptySort ()
      refine ⟨x,x,?_⟩
      simpa only [networkWord,frameWords,hc,if_pos hl,Option.getD_some,hword] using E.val.refl x
    · simp only [frameWords,hc,if_neg hl] at he
      exact (he rfl).elim

include H in
/-- C05--C07 in protected-frame form.  Every original recorded edge,
every protected value and every prescribed actual E-owner is retained.
The source instance of the private network is constructed here. -/
theorem protected_frame_completion (cco : SemanticCCO.{0,v,0,w} S)
    (E : ColourEq S ()) (hne : E ≠ ⊥) (word : RawWord S () ())
    (hword : RawWord.relation S word = E.val.r)
    (T : Finset (Fin n)) (complete : RawRecords.CompleteOn S D T)
    (owner base : Fin n → M) (hbase : RawRecords.Hom S D base)
    (hOwner : ∀ x y a, D.edge x y = some a →
      ownerSaturate E.val (S.atomRel a) (owner x) (owner y))
    (hT : ∀ x ∈ T, E (owner x) (base x))
    (hRep : ∀ x, rep x ∈ T ∧ E (owner x) (base (rep x))) :
    ∃ f : Fin n → M, RawRecords.Hom S D f ∧ (∀ x, E (owner x) (f x)) ∧
      ∀ x ∈ T, f x = base x := by
  classical
  let W := frameWords S D rep word
  have hnonempty := frameWords_nonempty S D rep word E hword
  have hLink (e : Edge n) (he : frameLink rep e) : E (owner (left e)) (owner (right e)) := by
    rcases he with hl | hr
    · have hh := (hRep (left e)).2
      rw [hl] at hh
      have ht := hT _ (hRep (left e)).1
      rw [hl] at ht
      exact E.val.trans hh (E.val.symm ht)
    · have hh := (hRep (right e)).2
      rw [hr] at hh
      exact E.val.symm (E.val.trans hh (E.val.symm (hT _ (by rw [← hr]; exact (hRep _).1))))
  have hPositive : ∀ e, W e ≠ none → 0 < diversityLength S (networkWord S W e) := by
    intro e he
    cases hc : D.edge (left e) (right e) with
    | some a => simp only [W,networkWord,frameWords,hc,Option.getD_some,diversityLength]; omega
    | none =>
      by_cases hl : frameLink rep e
      · have hh := represented_nonidentity_length S E hne word hword
        simpa only [W,networkWord,frameWords,hc,if_pos hl,Option.getD_some] using
          (show 0 < diversityLength S word by omega)
      · simp only [W,frameWords,hc,if_neg hl] at he
        exact (he rfl).elim
  have hOwn : ∀ e, W e ≠ none → ownerSaturate E.val
      (RawWord.relation S (networkWord S W e)) (owner (left e)) (owner (right e)) := by
    intro e he
    cases hc : D.edge (left e) (right e) with
    | some a =>
      simpa only [W,networkWord,frameWords,hc,Option.getD_some,direct_word_is_atom,AtomicSource.atomRel] using
        hOwner _ _ a hc
    | none =>
      by_cases hl : frameLink rep e
      · change ownerSaturate E.val (RawWord.relation S (networkWord S W e)) _ _
        simp only [W,networkWord,frameWords,hc,if_pos hl,Option.getD_some,hword]
        exact ⟨_,⟨_,hLink e hl,E.val.refl _⟩,E.val.refl _⟩
      · simp only [W,frameWords,hc,if_neg hl] at he
        exact (he rfl).elim
  have hBase : ∀ e, W e ≠ none → RawWord.relation S (networkWord S W e) ≠ E.val.r →
      RawWord.relation S (networkWord S W e) (base (left e)) (base (right e)) := by
    intro e he hne
    cases hc : D.edge (left e) (right e) with
    | some a =>
      simpa only [W,networkWord,frameWords,hc,Option.getD_some,direct_word_is_atom,AtomicSource.atomRel] using
        hbase _ _ a hc
    | none =>
      by_cases hl : frameLink rep e
      · apply False.elim
        apply hne
        simp only [W,networkWord,frameWords,hc,if_pos hl,Option.getD_some,hword]
      · simp only [W,frameWords,hc,if_neg hl] at he
        exact (he rfl).elim
  obtain ⟨hom⟩ := network_completion S H W hnonempty cco E owner base hPositive hOwn hBase
  let f : Fin n → M := fun x => hom.point (mark S networkSort (networkMenus S W) x)
  have hWord (e : Edge n) (he : W e ≠ none) :
      RawWord.relation S (networkWord S W e) (f (left e)) (f (right e)) := by
    apply hom_all_menus S networkSort (networkMenus S W) (network_nonempty S W hnonempty)
      hom ?_ e _ (network_word_mem S W e he)
    intro o
    have hm := network_mem_eq S W o.1 _ (List.get_mem _ o.2)
    change 0 < diversityLength S ((networkMenus S W o.1).get o.2)
    rw [hm.2]
    exact hPositive o.1 hm.1
  have hf : RawRecords.Hom S D f := by
    intro x y a hxy
    have hne : x ≠ y := by intro h; subst y; rw [D.diagonal] at hxy; cases hxy
    by_cases hlt : x < y
    · let e : Edge n := ⟨(x,y),hlt⟩
      have he : W e = some (.atom a (.nil ())) := frameWords_atom S D rep word e a hxy
      have hh := hWord e (by rw [he]; simp)
      change S.atomRel a (f (left e)) (f (right e))
      simpa only [networkWord,he,Option.getD_some,direct_word_is_atom] using hh
    · have hlt' : y < x := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
      let e : Edge n := ⟨(y,x),hlt'⟩
      have hrev : D.edge y x = some a := (D.symmetric y x).trans hxy
      have he : W e = some (.atom a (.nil ())) := frameWords_atom S D rep word e a hrev
      have hh := hWord e (by rw [he]; simp)
      exact (colour_symmetric S (f x) (f y)).trans
        (by
          change S.atomRel a (f (left e)) (f (right e))
          simpa only [networkWord,he,Option.getD_some,direct_word_is_atom] using hh)
  have hEqLink (e : Edge n) (hl : frameLink rep e) : E (f (left e)) (f (right e)) := by
    cases hc : D.edge (left e) (right e) with
    | some a =>
      exact saturated_atom_same_owner S E a (hLink e hl) (hOwner _ _ a hc)
        _ _ (hf _ _ a hc)
    | none =>
      have he : W e = some word := by simp only [W,frameWords,hc,if_pos hl]
      have hh := hWord e (by rw [he]; simp)
      simpa only [networkWord,he,Option.getD_some,hword] using hh
  have hRepEq (x : Fin n) : E (f x) (f (rep x)) := by
    by_cases hx : x = rep x
    · rw [← hx]
    · by_cases hlt : x < rep x
      · exact hEqLink ⟨(x,rep x),hlt⟩ (Or.inl rfl)
      · have hlt' : rep x < x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hx)
        exact E.val.symm (hEqLink ⟨(rep x,x),hlt'⟩ (Or.inr rfl))
  obtain ⟨g,hg⟩ := align_complete_frame S H D T complete f base hf hbase
  refine ⟨fun x => g • f x,?_,?_,hg⟩
  · intro x y a ha
    exact (S.colourInvariant_of_homogeneous H g (f x) (f y)).trans (hf x y a ha)
  · intro x
    have hh := colourInvariant_groupInvariant S H E.property g _ _ (hRepEq x)
    rw [hg _ (hRep x).1] at hh
    exact E.val.trans (hRep x).2 (E.val.symm hh)

end Construction

include H in
/-- The protected-frame theorem is independent of a chosen enumeration
of its finite formal vertices. -/
theorem protected_finite_frame_completion {V : Type} [Finite V]
    (D : RawRecords S V) (rep : V → V)
    (cco : SemanticCCO.{0,v,0,w} S) (E : ColourEq S ()) (hne : E ≠ ⊥)
    (word : RawWord S () ()) (hword : RawWord.relation S word = E.val.r)
    (T : Finset V) (complete : RawRecords.CompleteOn S D T)
    (owner base : V → M) (hbase : RawRecords.Hom S D base)
    (hOwner : ∀ x y a, D.edge x y = some a →
      ownerSaturate E.val (S.atomRel a) (owner x) (owner y))
    (hT : ∀ x ∈ T, E (owner x) (base x))
    (hRep : ∀ x, rep x ∈ T ∧ E (owner x) (base (rep x))) :
    ∃ f : V → M, RawRecords.Hom S D f ∧ (∀ x, E (owner x) (f x)) ∧
      ∀ x ∈ T, f x = base x := by
  classical
  letI := Fintype.ofFinite V
  let e := Fintype.equivFin V
  let D' : RawRecords S (Fin (Fintype.card V)) := {
    edge := fun x y => D.edge (e.symm x) (e.symm y)
    diagonal := fun x => D.diagonal _
    symmetric := fun x y => D.symmetric _ _ }
  let T' := T.map e.toEmbedding
  obtain ⟨f,hf,hown,hfix⟩ := protected_frame_completion S H D'
    (fun x => e (rep (e.symm x))) cco E hne word hword T'
    (fun x hx y hy hxy => by
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hy
      simpa only [D',Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using complete a ha b hb
        (fun hh => hxy (congrArg e hh)))
    (fun x => owner (e.symm x)) (fun x => base (e.symm x))
    (fun x y a ha => hbase _ _ a ha)
    (fun x y a ha => hOwner _ _ a ha)
    (fun x hx => by
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
      simpa only [Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using hT a ha)
    (fun x => ⟨Finset.mem_map.mpr ⟨_,(hRep (e.symm x)).1,rfl⟩,
      by simpa only [Equiv.symm_apply_apply] using (hRep (e.symm x)).2⟩)
  refine ⟨fun x => f (e x),?_,?_,?_⟩
  · intro x y a ha
    apply hf (e x) (e y) a
    simpa only [D',Equiv.symm_apply_apply] using ha
  · intro x
    simpa only [Equiv.symm_apply_apply] using hown (e x)
  · intro x hx
    simpa only [Equiv.symm_apply_apply] using hfix (e x) (Finset.mem_map.mpr ⟨x,hx,rfl⟩)

end CCO.OwnerTransversal
