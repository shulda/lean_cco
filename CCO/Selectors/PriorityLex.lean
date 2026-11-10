import CCO.Selectors.PriorityChain

/-!
# Lexicographic maximizers of the actual global gate descent

The numerical code is a radix encoding of the ordered fixed-stage score
vector. Its argmax on an original menu is exactly the composite gate,
including the empty-chain case. No menu-specific stage family is chosen.
-/

universe u v w z t
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {Λ : Type z} [Group Λ] {N : Type t}

/-- Every surviving atom attains a maximum of the fixed full-chain score,
while each removed original atom has strictly smaller score. -/
theorem descentScore_compare (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat}
    (chain : DescentChain S (IsVisibleGate S A) J K n) :
    ∀ {i j} (D : S.Menu i j),
      (⟨i,j,D⟩ : TaggedMenu S) ∈ J →
      ∀ (a : S.Atom i j),
      a ∈ (DescentChain.composite chain).toFun D →
      ∀ (b : S.Atom i j), b ∈ D →
        descentScore S A chain b ≤ descentScore S A chain a ∧
        (b ∉ (DescentChain.composite chain).toFun D →
          descentScore S A chain b < descentScore S A chain a) := by
  induction chain with
  | nil J =>
      intro i j D hD a ha b hb
      change (0 : Nat) ≤ 0 ∧ (b ∉ D → (0 : Nat) < 0)
      exact ⟨Nat.le_refl 0, fun hnot => False.elim (hnot hb)⟩
  | @cons J K L n R hRank tail ih =>
      intro i j D hD a ha b hb
      change a ∈ (DescentChain.composite tail).toFun (R.val.toFun D) at ha
      let F := stageFilter S A R
      have hF := (stageFilter_sound S A R).1
      have hEq : R.val.toFun D = gate S F D :=
        (stageFilter_sound S A R).2 D
      have haR : a ∈ R.val.toFun D :=
        (DescentChain.composite tail).conservative (R.val.maps hD) ha
      have haGate : a ∈ gate S F D := by rw [← hEq]; exact haR
      by_cases hbGate : b ∈ gate S F D
      · have hbR : b ∈ R.val.toFun D := by rw [hEq]; exact hbGate
        have htail := ih (R.val.toFun D) (R.val.maps hD) a ha b hbR
        have heq := symmetricScore_eq_of_gate S F hF D haGate hbGate
        constructor
        · change symmetricScore S F b * (scoreBase S i j)^n +
            descentScore S A tail b ≤
            symmetricScore S F a * (scoreBase S i j)^n +
            descentScore S A tail a
          rw [heq]
          exact Nat.add_le_add_left htail.1 _
        · intro hnot
          have hnotTail : b ∉ (DescentChain.composite tail).toFun (R.val.toFun D) := hnot
          change symmetricScore S F b * (scoreBase S i j)^n +
            descentScore S A tail b <
            symmetricScore S F a * (scoreBase S i j)^n +
            descentScore S A tail a
          rw [heq]
          exact Nat.add_lt_add_left (htail.2 hnotTail) _
      · have hweightStrict := symmetricScore_strict_of_gate S F hF D haGate hb hbGate
        have hrem := descentScore_lt_pow S A tail b
        have hdominates :
            symmetricScore S F b * (scoreBase S i j)^n +
              descentScore S A tail b <
            symmetricScore S F a * (scoreBase S i j)^n := by
          calc
            _ < symmetricScore S F b * (scoreBase S i j)^n +
                  (scoreBase S i j)^n := Nat.add_lt_add_left hrem _
            _ = (symmetricScore S F b + 1) * (scoreBase S i j)^n := by
                  simp [add_mul]
            _ ≤ symmetricScore S F a * (scoreBase S i j)^n :=
              Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hweightStrict)
        have hresult :
            symmetricScore S F b * (scoreBase S i j)^n +
              descentScore S A tail b <
            symmetricScore S F a * (scoreBase S i j)^n +
              descentScore S A tail a :=
          lt_of_lt_of_le hdominates (Nat.le_add_right _ _)
        constructor
        · change symmetricScore S F b * (scoreBase S i j)^n +
            descentScore S A tail b ≤
            symmetricScore S F a * (scoreBase S i j)^n +
            descentScore S A tail a
          exact le_of_lt hresult
        · intro _
          change symmetricScore S F b * (scoreBase S i j)^n +
            descentScore S A tail b <
            symmetricScore S F a * (scoreBase S i j)^n +
            descentScore S A tail a
          exact hresult

/-- The global chain selects exactly the maximizers of its one numeric
original-atom score. Current-family exactness provides the attained maximum. -/
theorem descentScore_argmax (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat}
    (chain : DescentChain S (IsVisibleGate S A) J K n)
    (hK : CurrentFamily S K)
    {i j : ι} (D : S.Menu i j)
    (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J) :
    (DescentChain.composite chain).toFun D =
      {a | a ∈ D ∧ ∀ b ∈ D,
        descentScore S A chain b ≤ descentScore S A chain a} := by
  ext a
  constructor
  · intro ha
    exact ⟨(DescentChain.composite chain).conservative hD ha,
      fun b hb => (descentScore_compare S A chain D hD a ha b hb).1⟩
  · rintro ⟨haD,hmax⟩
    have hExact : StrongExact.Exact S
        ((DescentChain.composite chain).toFun D) :=
      hK.exact ((DescentChain.composite chain).maps hD)
    obtain ⟨c,hc⟩ := hExact.1
    have hcD : c ∈ D := (DescentChain.composite chain).conservative hD hc
    by_contra hnot
    have hlt := (descentScore_compare S A chain D hD c hc a haD).2 hnot
    exact (not_lt_of_ge (hmax c hcD)) hlt

/-- Terminality makes the chosen atom the unique maximizer on each original
exact menu, rather than merely one among tied maximizers. -/
theorem terminal_descent_strict_winner (A : PureTagAction S Λ N)
    {K : Family S} {n : Nat}
    (chain : DescentChain S (IsVisibleGate S A) (originalFamily S) K n)
    (hTerm : Terminal S K) {i j : ι} (D : S.Menu i j)
    (hD : StrongExact.Exact S D)
    (b : S.Atom i j) (hb : b ∈ D)
    (hneq : b ≠ (selectorOfTerminal S hTerm
      (DescentChain.composite chain)).choose D hD) :
    descentScore S A chain b <
      descentScore S A chain ((selectorOfTerminal S hTerm
        (DescentChain.composite chain)).choose D hD) := by
  let h := selectorOfTerminal S hTerm (DescentChain.composite chain)
  have hsingle := selectorOfTerminal_singleton S hTerm
    (DescentChain.composite chain) D hD
  have ha : h.choose D hD ∈ (DescentChain.composite chain).toFun D := by
    rw [hsingle]
    exact Set.mem_singleton _
  have hbNot : b ∉ (DescentChain.composite chain).toFun D := by
    rw [hsingle]
    exact hneq
  exact (descentScore_compare S A chain D hD (h.choose D hD) ha b hb).2 hbNot

end CCO.Selectors
