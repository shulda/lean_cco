import CCO.SafeReadings.PrimitivePowers
import CCO.PositiveWords
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Chain

/-! Positive prefixes only: the state after the first actual diversity
letter is the first state. There is no empty STRONG word or identity menu. -/
universe u v w
namespace CCO.HKNReservoir.Locality
open SafeReadings Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def wordLength {i j : ι} : PositiveWord S i j → Nat
  | .single _ => 1
  | .cons _ tail => wordLength tail + 1

theorem wordLength_pos {i j : ι} (word : PositiveWord S i j) :
    0 < wordLength S word := by
  cases word <;> simp [wordLength]

abbrev RowMenu (s : ι) := Σ t, S.Menu s t
def properStates (s : ι) := Σ t, {D : S.Menu s t // D.Nonempty ∧ D ≠ Set.univ}

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

end Source
end CCO.HKNReservoir.Locality
