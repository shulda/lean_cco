import CCO.GuardedTwoRoot.TypedPrefixChains
import CCO.PositiveWords
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card

/-! Actual typed positive prefix states. Both endpoint sorts are
retained, and every menu is NONEMPTY. There is no empty prefix, real-Id
state or STRONG unit. All algebra below is instantiated from original
homogeneous SAP, not an abstract associativity provider. -/

universe u v w r
namespace CCO.GuardedTwoRoot.TypedPrefix
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def length {i j : ι} : PositiveWord S i j → ℕ
  | .single _ => 1
  | .cons _ rest => length rest + 1

theorem length_pos {i j : ι} (word : PositiveWord S i j) : 0 < length S word := by
  cases word <;> simp only [length] <;> omega

theorem length_append {i j k : ι} (first : PositiveWord S i j) (second : PositiveWord S j k) :
    length S (PositiveWord.append S first second) = length S first + length S second := by
  induction first with
  | single a => simp only [PositiveWord.append,length]; omega
  | cons a rest ih => simp only [PositiveWord.append,length,ih]; omega

/-- The initial sort is a type index; the current end sort is actual
state data. Erasing either tag would make loop deletion ill-typed. -/
abbrev RowState (i : ι) := Σ j : ι, {P : S.Menu i j // P.Nonempty}
abbrev State := Σ i : ι, RowState S i

instance rowState_finite (i : ι) : Finite (RowState S i) := by
  classical
  letI : Fintype ι := S.finiteSort
  letI (j : ι) : Fintype (S.Atom i j) := S.finiteAtom i j
  letI (j : ι) : Fintype (S.Menu i j) := Fintype.ofFinite _
  infer_instance

instance state_finite : Finite (State S) := by
  classical
  letI : Fintype ι := S.finiteSort
  letI (i : ι) : Fintype (RowState S i) := Fintype.ofFinite _
  infer_instance

def Step {i : ι} (p q : RowState S i) : Prop :=
  ∃ a : S.Atom p.1 q.1, q.2.val = S.product p.2.val {a}

def singletonState {i j : ι} (a : S.Atom i j) : RowState S i := ⟨j,⟨{a},a,rfl⟩⟩

section Source
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

def shift {i j : ι} (a : S.Atom i j) (p : RowState S j) : RowState S i :=
  ⟨p.1,⟨S.product {a} p.2.val,
    S.product_nonempty_of_point_gluing (S.realPointGluing_of_SAP H sap) ⟨a,rfl⟩ p.2.property⟩⟩

def trace {i j : ι} : PositiveWord S i j → List (RowState S i)
  | .single a => [singletonState S a]
  | .cons a rest => singletonState S a :: (trace rest).map (shift S H sap a)

theorem trace_length {i j : ι} (word : PositiveWord S i j) :
    (trace S H sap word).length = length S word := by
  induction word with
  | single a => rfl
  | cons a rest ih => simp only [trace,List.length_cons,List.length_map,length,ih]

theorem trace_ne_nil {i j : ι} (word : PositiveWord S i j) : trace S H sap word ≠ [] := by
  cases word <;> simp [trace]

theorem step_shift {i j : ι} (a : S.Atom i j) {p q : RowState S j}
    (h : Step S p q) : Step S (shift S H sap a p) (shift S H sap a q) := by
  obtain ⟨b,hb⟩ := h
  refine ⟨b,?_⟩
  change S.product {a} q.2.val = S.product (S.product {a} p.2.val) {b}
  rw [hb,S.product_assoc_of_edge_gluing (S.realEdgeGluing_of_SAP H sap)]

theorem trace_chain {i j : ι} (word : PositiveWord S i j) :
    (trace S H sap word).IsChain (Step S) := by
  induction word with
  | single a => exact List.IsChain.singleton _
  | cons a rest ih =>
    have hm := List.isChain_map_of_isChain (shift S H sap a)
      (fun _ _ h => step_shift S H sap a h) ih
    cases rest with
    | single b => exact List.isChain_cons_cons.mpr ⟨⟨b,rfl⟩,hm⟩
    | cons b tail => exact List.isChain_cons_cons.mpr ⟨⟨b,rfl⟩,hm⟩

def finalState {i j : ι} (word : PositiveWord S i j) : RowState S i :=
  ⟨j,⟨PositiveWord.profile S word,PositiveWord.profile_nonempty_of_SAP S H sap word⟩⟩

theorem trace_last {i j : ι} (word : PositiveWord S i j) :
    (trace S H sap word).getLast? = some (finalState S H sap word) := by
  induction word with
  | single a => rfl
  | cons a rest ih =>
    change (singletonState S a :: (trace S H sap rest).map (shift S H sap a)).getLast? = _
    have hMap : (trace S H sap rest).map (shift S H sap a) ≠ [] := by
      cases hTrace : trace S H sap rest with
      | nil => exact False.elim (trace_ne_nil S H sap rest hTrace)
      | cons b bs => simp
    rw [List.getLast?_cons_of_ne_nil hMap, List.getLast?_map,ih]
    rfl

theorem trace_first {i j : ι} (word : PositiveWord S i j) :
    ∃ (k : ι) (a : S.Atom i k), (trace S H sap word).head? = some (singletonState S a) := by
  cases word with
  | single a => exact ⟨_,a,rfl⟩
  | cons a rest => exact ⟨_,a,rfl⟩

/-- Reconstruct an actual positive word along a directed profile trace.
The starting word is retained, so even a zero-step suffix stays positive. -/
include H sap

theorem realise_chain {i : ι} (target : RowState S i) (tail : List (RowState S i)) :
    ∀ (p : RowState S i) (word : PositiveWord S i p.1),
      PositiveWord.profile S word = p.2.val →
      (p :: tail).IsChain (Step S) → (p :: tail).getLast? = some target →
      ∃ out : PositiveWord S i target.1,
        PositiveWord.profile S out = target.2.val ∧ length S out = length S word + tail.length := by
  induction tail with
  | nil =>
    intro p word hWord hChain hLast
    have he : p = target := Option.some.inj hLast
    cases he
    exact ⟨word,hWord,by simp⟩
  | cons q tail ih =>
    intro p word hWord hChain hLast
    obtain ⟨a,ha⟩ := (List.isChain_cons_cons.mp hChain).1
    let next : PositiveWord S i q.1 := PositiveWord.append S word (.single a)
    have hNext : PositiveWord.profile S next = q.2.val := by
      rw [PositiveWord.profile_append_of_SAP S H sap,hWord]
      exact ha.symm
    obtain ⟨out,hOut,hLen⟩ := ih q next hNext (List.isChain_cons_cons.mp hChain).2
      (by simpa only [List.getLast?_cons_cons] using hLast)
    refine ⟨out,hOut,?_⟩
    have hNextLen : length S next = length S word + 1 := length_append S word (.single a)
    simp only [List.length_cons]
    omega

/-- A state-chain with the same first positive letter and last state
gives a positive presentation whose letter count is its state count. -/
theorem word_of_chain {i j : ι} (a : S.Atom i j) (target : RowState S i)
    (nodes : List (RowState S i)) (hChain : nodes.IsChain (Step S))
    (hHead : nodes.head? = some (singletonState S a)) (hLast : nodes.getLast? = some target) :
    ∃ word : PositiveWord S i target.1,
      PositiveWord.profile S word = target.2.val ∧ length S word = nodes.length := by
  cases nodes with
  | nil => simp only [List.head?_nil] at hHead; cases hHead
  | cons p tail =>
    have he : p = singletonState S a := Option.some.inj hHead
    subst p
    obtain ⟨word,hWord,hLen⟩ := realise_chain S H sap target tail (singletonState S a)
      (.single a) rfl hChain hLast
    exact ⟨word,hWord,by simpa only [length,List.length_cons,Nat.add_comm] using hLen⟩

end Source
end CCO.GuardedTwoRoot.TypedPrefix
