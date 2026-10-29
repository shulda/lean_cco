import CCO.SafeReadings.PrimitivePowers
import CCO.PositiveWords
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Nodup

/-! Positive prefixes only: the state after the first actual diversity
letter is the first state. There is no empty STRONG word or identity menu. -/
universe u v w
namespace CCO.HKNReservoir.Locality
open SafeReadings Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
local instance (i j : ι) : Fintype (S.Atom i j) := S.finiteAtom i j

def wordLength {i j : ι} : PositiveWord S i j → Nat
  | .single _ => 1
  | .cons _ tail => wordLength tail + 1

theorem wordLength_pos {i j : ι} (word : PositiveWord S i j) :
    0 < wordLength S word := by
  cases word <;> simp [wordLength]

abbrev RowMenu (s : ι) := Σ t, S.Menu s t
def properStates (s : ι) := Σ t, {D : S.Menu s t // D.Nonempty ∧ D ≠ Set.univ}

local instance (s : ι) : Finite (properStates S s) := by
  classical
  let := S.finiteSort
  unfold properStates
  infer_instance

def shift {i j : ι} (a : S.Atom i j) (p : RowMenu S j) : RowMenu S i :=
  ⟨p.1,S.product {a} p.2⟩

def trace {i j : ι} : PositiveWord S i j → List (RowMenu S i)
  | .single a => [⟨_,{a}⟩]
  | .cons a tail => ⟨_,{a}⟩ :: (trace tail).map (shift S a)

theorem trace_length {i j : ι} (word : PositiveWord S i j) :
    (trace S word).length = wordLength S word := by
  induction word with
  | single a => rfl
  | cons a tail ih => simp only [trace,List.length_cons,List.length_map,wordLength,ih]

theorem trace_ne_nil {i j : ι} (word : PositiveWord S i j) : trace S word ≠ [] := by
  cases word <;> simp [trace]

def Step {s : ι} (p q : RowMenu S s) : Prop :=
  ∃ a : S.Atom p.1 q.1, q.2 = S.product p.2 {a}

section Source
variable {G : Type*} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

include H sap in
theorem step_shift {i j : ι} (a : S.Atom i j) {p q : RowMenu S j}
    (h : Step S p q) : Step S (shift S a p) (shift S a q) := by
  obtain ⟨b,hb⟩ := h
  refine ⟨b,?_⟩
  change S.product {a} q.2 = S.product (S.product {a} p.2) {b}
  rw [hb,S.product_assoc_of_edge_gluing (S.realEdgeGluing_of_SAP H sap)]

include H sap in
theorem trace_chain {i j : ι} (word : PositiveWord S i j) :
    (trace S word).IsChain (Step S) := by
  induction word with
  | single a => simp [trace]
  | cons a tail ih =>
    have hm := List.isChain_map_of_isChain (shift S a)
      (fun _ _ h => step_shift S H sap a h) ih
    cases tail with
    | single b =>
      exact List.isChain_cons_cons.mpr ⟨⟨b,rfl⟩,hm⟩
    | cons b rest =>
      exact List.isChain_cons_cons.mpr ⟨⟨b,rfl⟩,hm⟩

theorem trace_last {i j : ι} (word : PositiveWord S i j) :
    (trace S word).getLast (trace_ne_nil S word) = ⟨j,PositiveWord.profile S word⟩ := by
  induction word with
  | single a => rfl
  | cons a tail ih =>
    change (⟨_,{a}⟩ :: (trace S tail).map (shift S a)).getLast _ =
      ⟨_,S.product {a} (PositiveWord.profile S tail)⟩
    rw [List.getLast_cons (by simpa using trace_ne_nil S tail),List.getLast_map,ih]
    rfl

include H sap in
theorem step_path_word {s : ι} {p q : RowMenu S s}
    (h : Relation.TransGen (Step S) p q) :
    ∃ word : PositiveWord S p.1 q.1,
      q.2 = S.product p.2 (PositiveWord.profile S word) := by
  induction h with
  | single h =>
    obtain ⟨a,ha⟩ := h
    exact ⟨.single a,ha⟩
  | @tail q r hPath hStep ih =>
    obtain ⟨word,hw⟩ := ih
    obtain ⟨a,ha⟩ := hStep
    refine ⟨PositiveWord.append S word (.single a),?_⟩
    rw [PositiveWord.profile_append_of_SAP S H sap]
    change r.2 = S.product p.2 (S.product (PositiveWord.profile S word) {a})
    rw [← S.product_assoc_of_edge_gluing (S.realEdgeGluing_of_SAP H sap),← hw]
    exact ha

include H sap in
theorem proper_return_impossible (primitive : SortwisePrimitive S)
    {s t : ι} (D : S.Menu s t) (hD : D.Nonempty) (hProper : D ≠ Set.univ)
    (W : S.Menu t t) (hW : W.Nonempty) (hReturn : S.product D W = D) : False := by
  have hPowers : ∀ n, S.product D (loopPower S W n) = D := by
    intro n
    induction n with
    | zero => simpa only [loopPower] using hReturn
    | succ n ih =>
      rw [loopPower_succ, ← S.product_assoc_of_edge_gluing
        (S.realEdgeGluing_of_SAP H sap), ih, hReturn]
  have hFull := primitive_loopPower_full_of_SAP S H primitive W hW sap
  have hEq := hPowers (2 * Nat.card (S.Atom t t) - 1)
  rw [hFull,source_product_top S H sap D hD] at hEq
  exact hProper hEq.symm

def ProperStep {s : ι} (p q : RowMenu S s) : Prop :=
  p.2.Nonempty ∧ p.2 ≠ Set.univ ∧ q.2.Nonempty ∧ q.2 ≠ Set.univ ∧ Step S p q

include H sap in
theorem proper_step_acyclic (primitive : SortwisePrimitive S) {s : ι}
    (p : RowMenu S s) : ¬ Relation.TransGen (ProperStep S) p p := by
  intro h
  obtain ⟨q,hFirst,_⟩ := Relation.TransGen.head'_iff.mp h
  have hp : p.2.Nonempty ∧ p.2 ≠ Set.univ := ⟨hFirst.1,hFirst.2.1⟩
  have plain : Relation.TransGen (Step S) p p :=
    Relation.TransGen.mono (by intro a b hab; exact hab.2.2.2.2) p p h
  obtain ⟨word,hw⟩ := step_path_word S H sap plain
  exact proper_return_impossible S H sap primitive p.2 hp.1 hp.2
    (PositiveWord.profile S word) (PositiveWord.profile_nonempty_of_SAP S H sap word) hw.symm

include H sap in
theorem trace_nonempty {i j : ι} (word : PositiveWord S i j) :
    ∀ p ∈ trace S word, p.2.Nonempty := by
  induction word with
  | single a =>
    intro p hp
    have he : p = ⟨_,{a}⟩ := by simpa only [trace,List.mem_singleton] using hp
    subst p
    exact ⟨a,rfl⟩
  | cons a tail ih =>
    intro p hp
    rcases List.mem_cons.mp hp with he | hm
    · subst p; exact ⟨a,rfl⟩
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm
      exact S.product_nonempty_of_point_gluing (S.realPointGluing_of_SAP H sap)
        ⟨a,rfl⟩ (ih q hq)

include H sap in
theorem step_full {s : ι} {p q : RowMenu S s} (h : Step S p q)
    (hp : p.2 = Set.univ) : q.2 = Set.univ := by
  obtain ⟨a,ha⟩ := h
  rw [ha,hp,source_top_product S H sap {a} (Set.singleton_nonempty a)]

include H sap in
theorem path_full {s : ι} {p q : RowMenu S s}
    (h : Relation.ReflTransGen (Step S) p q) : p.2 = Set.univ → q.2 = Set.univ := by
  induction h with
  | refl => exact id
  | tail _ hStep ih => exact fun hp => step_full S H sap hStep (ih hp)

include H sap in
theorem trace_proper {i j : ι} (word : PositiveWord S i j)
    (hFinal : PositiveWord.profile S word ≠ Set.univ) :
    ∀ p ∈ trace S word, p.2 ≠ Set.univ := by
  intro p hp hpFull
  have hc := (trace_chain S H sap word).imp
    (fun {_ _} h => Relation.ReflTransGen.single h)
  have reach := hc.pairwise.rel_getLast hp
  have he := path_full S H sap reach hpFull
  rw [trace_last S word] at he
  exact hFinal he

include H sap in
theorem trace_nodup (primitive : SortwisePrimitive S) {i j : ι}
    (word : PositiveWord S i j) (hFinal : PositiveWord.profile S word ≠ Set.univ) :
    (trace S word).Nodup := by
  have hc := trace_chain S H sap word
  have hProper : (trace S word).IsChain (ProperStep S) := by
    apply List.isChain_iff_getElem.mpr
    intro k hk
    have hk0 : k < (trace S word).length := by omega
    have hp := List.getElem_mem hk0
    have hq := List.getElem_mem hk
    exact ⟨trace_nonempty S H sap word _ hp,trace_proper S H sap word hFinal _ hp,
      trace_nonempty S H sap word _ hq,trace_proper S H sap word hFinal _ hq,hc.getElem k hk⟩
  have hpw := (hProper.imp (fun {_ _} h => Relation.TransGen.single h)).pairwise
  exact hpw.imp fun {p q} h he => by
    subst q
    exact proper_step_acyclic S H sap primitive p h

end Source

theorem card_proper_menus (A : Type w) [Fintype A] :
    Nat.card {D : Set A // D.Nonempty ∧ D ≠ Set.univ} = 2 ^ Nat.card A - 2 := by
  classical
  rcases isEmpty_or_nonempty A with hEmpty | hNonempty
  · let := hEmpty
    let : IsEmpty {D : Set A // D.Nonempty ∧ D ≠ Set.univ} :=
      ⟨fun D => let ⟨a,_⟩ := D.2.1; isEmptyElim a⟩
    simp [Nat.card_eq_fintype_card,Fintype.card_eq_zero]
  · let := hNonempty
    let good : Finset (Set A) := ((Finset.univ : Finset (Set A)).erase ∅).erase Set.univ
    let e : {D : Set A // D.Nonempty ∧ D ≠ Set.univ} ≃ ↥good := {
      toFun := fun D => ⟨D.1,by
        simp only [good,Finset.mem_erase,Finset.mem_univ,and_true]
        exact ⟨D.2.2,D.2.1.ne_empty⟩⟩
      invFun := fun D => ⟨D.1,by
        have hd := D.2
        simp only [good,Finset.mem_erase,Finset.mem_univ,and_true] at hd
        exact ⟨Set.nonempty_iff_ne_empty.mpr hd.2,hd.1⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have hNe : (Set.univ : Set A) ≠ ∅ := Set.univ_nonempty.ne_empty
    calc
      Nat.card {D : Set A // D.Nonempty ∧ D ≠ Set.univ} = Nat.card ↥good := Nat.card_congr e
      _ = good.card := by simp only [Nat.card_eq_fintype_card,Fintype.card_coe]
      _ = 2 ^ Nat.card A - 2 := by
        dsimp [good]
        rw [Finset.card_erase_of_mem (by simp [hNe]),
          Finset.card_erase_of_mem (Finset.mem_univ _)]
        simp [Fintype.card_set,Nat.card_eq_fintype_card,Nat.sub_sub]

noncomputable def rowBound (s : ι) : Nat :=
  letI := S.finiteSort
  ∑ t, (2 ^ Nat.card (S.Atom s t) - 2)
noncomputable def localityBound : Nat :=
  letI := S.finiteSort
  Finset.univ.sup (rowBound S)
noncomputable def cycleBound : Nat := max 3 (localityBound S + 1)

theorem card_properStates (s : ι) : Nat.card (properStates S s) = rowBound S s := by
  classical
  let := S.finiteSort
  change Nat.card (Σ t, {D : S.Menu s t // D.Nonempty ∧ D ≠ Set.univ}) = _
  rw [Nat.card_sigma]
  unfold rowBound
  apply Finset.sum_congr rfl
  intro t _
  exact card_proper_menus (S.Atom s t)

theorem localityBound_zero_of_singletons (h : ∀ s t, Nat.card (S.Atom s t) = 1) :
    localityBound S = 0 := by
  have hCard (s t) : Fintype.card (S.Atom s t) = 1 := by
    simpa only [Nat.card_eq_fintype_card] using h s t
  simp [localityBound,rowBound,hCard]

section Bound
variable {G : Type*} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

include H sap in
theorem proper_length_bound (primitive : SortwisePrimitive S) {i j : ι}
    (word : PositiveWord S i j) (hFinal : PositiveWord.profile S word ≠ Set.univ) :
    wordLength S word ≤ rowBound S i := by
  classical
  let := S.finiteSort
  let f : Fin (trace S word).length → properStates S i := fun k =>
    ⟨((trace S word).get k).1,⟨((trace S word).get k).2,
      trace_nonempty S H sap word _ (List.get_mem _ _),
      trace_proper S H sap word hFinal _ (List.get_mem _ _)⟩⟩
  have hf : Function.Injective f := by
    intro a b he
    have hv := congrArg (fun p : properStates S i => (⟨p.1,p.2.1⟩ : RowMenu S i)) he
    exact (trace_nodup S H sap primitive word hFinal).injective_get hv
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_fin,trace_length,card_properStates] using hc

include H sap in
theorem profile_full_of_length_gt (primitive : SortwisePrimitive S) {i j : ι}
    (word : PositiveWord S i j) (hLength : localityBound S < wordLength S word) :
    PositiveWord.profile S word = Set.univ := by
  classical
  let := S.finiteSort
  by_contra hProper
  have hBound := proper_length_bound S H sap primitive word hProper
  have hRow : rowBound S i ≤ localityBound S := Finset.le_sup (Finset.mem_univ i)
  exact Nat.not_lt_of_ge (hBound.trans hRow) hLength

end Bound
end CCO.HKNReservoir.Locality
