import CCO.GuardedTwoRoot.TypedPrefixStates

/-! A shortest POSITIVE presentation has distinct nonempty typed prefix
states, hence at most card(State) letters. Return-loop deletion retains
the first prefix (index at least one); no identity word is used. -/

universe u v w r
namespace CCO.GuardedTwoRoot.TypedPrefix
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def Shortest {i j : ι} (word : PositiveWord S i j) : Prop :=
  ∀ out : PositiveWord S i j, PositiveWord.profile S out = PositiveWord.profile S word →
    length S word ≤ length S out

theorem exists_shortest_profile_word {i j : ι} (word : PositiveWord S i j) :
    ∃ out : PositiveWord S i j,
      PositiveWord.profile S out = PositiveWord.profile S word ∧ Shortest S out := by
  classical
  let prop : ℕ → Prop := fun n => ∃ out : PositiveWord S i j,
    PositiveWord.profile S out = PositiveWord.profile S word ∧ length S out = n
  have hExists : ∃ n, prop n := ⟨length S word,word,rfl,rfl⟩
  obtain ⟨out,hProfile,hLength⟩ := Nat.find_spec hExists
  refine ⟨out,hProfile,?_⟩
  intro other hOther
  rw [hLength]
  exact Nat.find_min' hExists ⟨other,hOther.trans hProfile,rfl⟩

section Source
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

/-- C25/C50: no repeated NONEMPTY prefix state of a shortest positive
word. The generic loop cut keeps its first positive singleton state and
reconstructs a shorter actual well-typed word if a repetition existed. -/
theorem shortest_trace_nodup {i j : ι} (word : PositiveWord S i j)
    (hShortest : Shortest S word) : (trace S H sap word).Nodup := by
  apply shortest_chain_nodup (trace S H sap word) (trace_chain S H sap word)
  intro nodes hChain hHead hLast
  obtain ⟨k,a,hFirst⟩ := trace_first S H sap word
  obtain ⟨out,hOut,hLength⟩ := word_of_chain S H sap a (finalState S H sap word) nodes hChain
    (hHead.trans hFirst) (hLast.trans (trace_last S H sap word))
  have hBound := hShortest out hOut
  rwa [hLength,← trace_length S H sap word] at hBound

/-- C26: both initial and current endpoint-sort tags occur in State.
Only positive profiles are counted; no real-Id state is adjoined. -/
theorem shortest_length_le_card_states {i j : ι} (word : PositiveWord S i j)
    (hShortest : Shortest S word) : length S word ≤ Nat.card (State S) := by
  let nodes := trace S H sap word
  let f : Fin nodes.length → State S := fun k => ⟨i,nodes.get k⟩
  have hf : Function.Injective f := by
    intro a b he
    have hv : nodes.get a = nodes.get b := sigma_mk_injective he
    exact (shortest_trace_nodup S H sap word hShortest).injective_get hv
  have hCard := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_fin,trace_length] using hCard

theorem bounded_positive_presentation {i j : ι} (P : S.Menu i j)
    (hReachable : ∃ word : PositiveWord S i j, PositiveWord.profile S word = P) :
    ∃ word : PositiveWord S i j,
      PositiveWord.profile S word = P ∧ Shortest S word ∧
      length S word ≤ Nat.card (State S) := by
  obtain ⟨original,hOriginal⟩ := hReachable
  obtain ⟨word,hProfile,hShortest⟩ := exists_shortest_profile_word S original
  exact ⟨word,hProfile.trans hOriginal,hShortest,
    shortest_length_le_card_states S H sap word hShortest⟩

/-- The finite family of actual reachable typed positive profiles. -/
abbrev ReachableState := {p : State S // ∃ word : PositiveWord S p.1 p.2.1,
  PositiveWord.profile S word = p.2.2.val}

instance reachableState_finite : Finite (ReachableState S) := inferInstance

/-- Choose ONCE for each profile, independent of any partial source or
chosen real representative. Unbounded unary syntax does not enter. -/
def fixedWord (p : ReachableState S) : PositiveWord S p.val.1 p.val.2.1 :=
  (bounded_positive_presentation S H sap p.val.2.2.val p.property).choose

theorem fixedWord_profile (p : ReachableState S) :
    PositiveWord.profile S (fixedWord S H sap p) = p.val.2.2.val :=
  (bounded_positive_presentation S H sap p.val.2.2.val p.property).choose_spec.1

theorem fixedWord_length (p : ReachableState S) :
    length S (fixedWord S H sap p) ≤ Nat.card (State S) :=
  (bounded_positive_presentation S H sap p.val.2.2.val p.property).choose_spec.2.2

end Source
end CCO.GuardedTwoRoot.TypedPrefix
