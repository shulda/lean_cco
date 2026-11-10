import CCO.Selectors.Priority
import Lean.Elab.Tactic.Omega

/-!
# Fixed scores of the actual globally chosen gate chain

Each edge stores a single filter family for all original menus at that stage.
The score of any atom is fixed independently of the input menu; no new
multiplication or conditional choice of a menu-specific filter is introduced.
-/

universe u v w z t
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {Λ : Type z} [Group Λ] {N : Type t}

/-- Adding the score of the converse atom enforces converse compatibility
without requiring any arbitrary choice of matching filter enumerations. -/
noncomputable def symmetricScore (F : Family S) {i j : ι}
    (a : S.Atom i j) : Nat :=
  incidenceScore S F a + incidenceScore S F (S.conv a)

theorem symmetricScore_opposite (F : Family S)
    {i j : ι} (a : S.Atom i j) :
    symmetricScore S F (S.conv a) = symmetricScore S F a := by
  simp only [symmetricScore, S.conv_invol, Nat.add_comm]

theorem incidenceScore_le_palette (F : Family S)
    {i j : ι} (a : S.Atom i j) :
    incidenceScore S F a ≤ Fintype.card (S.Menu i j) := by
  classical
  have hsub : filtersThrough S F a ⊆ (Finset.univ : Finset (S.Menu i j)) := by
    intro B _
    exact Finset.mem_univ B
  simpa only [incidenceScore, Finset.card_univ] using Finset.card_le_card hsub

/-- One radix for both directions of a named-sort pair. -/
noncomputable def scoreBase (i j : ι) : Nat :=
  Fintype.card (S.Menu i j) + Fintype.card (S.Menu j i) + 1

theorem scoreBase_pos (i j : ι) : 0 < scoreBase S i j := by
  unfold scoreBase
  omega

theorem scoreBase_reverse (i j : ι) :
    scoreBase S j i = scoreBase S i j := by
  simp only [scoreBase, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem symmetricScore_lt_base (F : Family S)
    {i j : ι} (a : S.Atom i j) :
    symmetricScore S F a < scoreBase S i j := by
  have h1 := incidenceScore_le_palette S F a
  have h2 := incidenceScore_le_palette S F (S.conv a)
  dsimp [symmetricScore, scoreBase]
  omega

private theorem gate_converse_mem (F : Family S) (hF : FilterFamily S F)
    {i j : ι} {D : S.Menu i j} {a : S.Atom i j}
    (ha : a ∈ gate S F D) :
    S.conv a ∈ gate S F (S.opposite D) := by
  rw [gate_opposite S hF D]
  exact S.mem_opposite ha

private theorem gate_converse_not_mem (F : Family S) (hF : FilterFamily S F)
    {i j : ι} {D : S.Menu i j} {b : S.Atom i j}
    (hb : b ∉ gate S F D) :
    S.conv b ∉ gate S F (S.opposite D) := by
  intro hb'
  rw [gate_opposite S hF D] at hb'
  change S.conv (S.conv b) ∈ gate S F D at hb'
  exact hb (by simpa only [S.conv_invol] using hb')

theorem symmetricScore_eq_of_gate (F : Family S) (hF : FilterFamily S F)
    {i j : ι} (D : S.Menu i j) {a b : S.Atom i j}
    (ha : a ∈ gate S F D) (hb : b ∈ gate S F D) :
    symmetricScore S F a = symmetricScore S F b := by
  have ha1 := (mem_gate_iff_incidenceScore_eq_active S F D a).mp ha
  have hb1 := (mem_gate_iff_incidenceScore_eq_active S F D b).mp hb
  have haOpp := gate_converse_mem S F hF ha
  have hbOpp := gate_converse_mem S F hF hb
  have ha2 := (mem_gate_iff_incidenceScore_eq_active S F (S.opposite D)
    (S.conv a)).mp haOpp
  have hb2 := (mem_gate_iff_incidenceScore_eq_active S F (S.opposite D)
    (S.conv b)).mp hbOpp
  dsimp [symmetricScore]
  omega

theorem symmetricScore_strict_of_gate (F : Family S) (hF : FilterFamily S F)
    {i j : ι} (D : S.Menu i j) {a b : S.Atom i j}
    (ha : a ∈ gate S F D) (hbD : b ∈ D)
    (hb : b ∉ gate S F D) :
    symmetricScore S F b < symmetricScore S F a := by
  have h1 := incidenceScore_strict_of_gate S F D ha hbD hb
  have haOpp := gate_converse_mem S F hF ha
  have hbOpp := gate_converse_not_mem S F hF hb
  have h2 := incidenceScore_strict_of_gate S F (S.opposite D)
    haOpp (S.mem_opposite hbD) hbOpp
  dsimp [symmetricScore]
  omega

/-- Select one single global filter, uniformly for all menus in this stage. -/
private noncomputable def stageFilter (A : PureTagAction S Λ N)
    {J K : Family S}
    (R : {R : Contraction S J K // IsVisibleGate S A R}) : Family S :=
  Classical.choose R.property.actual_gate

private theorem stageFilter_sound (A : PureTagAction S Λ N)
    {J K : Family S} (R : {R : Contraction S J K // IsVisibleGate S A R}) :
    FilterFamily S (stageFilter S A R) ∧
      ∀ {i j} (D : S.Menu i j), R.val.toFun D = gate S (stageFilter S A R) D := by
  exact ⟨(Classical.choose_spec R.property.actual_gate).1,
    (Classical.choose_spec R.property.actual_gate).2.2.2.2⟩

/-- A bounded-base encoding of the ordered sequence of gate scores.
The empty sequence is the constant score zero. -/
noncomputable def descentScore (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat}
    (chain : DescentChain S (IsVisibleGate S A) J K n)
    {i j : ι} (a : S.Atom i j) : Nat :=
  match chain with
  | .nil _ => 0
  | .cons (n := n) R _ tail =>
      symmetricScore S (stageFilter S A R) a * (scoreBase S i j)^n +
        descentScore S A tail a

theorem descentScore_reverse (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat}
    (chain : DescentChain S (IsVisibleGate S A) J K n) :
    ∀ {i j} (a : S.Atom i j),
      descentScore S A chain (S.conv a) = descentScore S A chain a := by
  induction chain with
  | nil J =>
      intro i j a
      rfl
  | cons R hstrict tail ih =>
      intro i j a
      change symmetricScore S (stageFilter S A R) (S.conv a) *
          (scoreBase S j i)^_ + descentScore S A tail (S.conv a) =
        symmetricScore S (stageFilter S A R) a *
          (scoreBase S i j)^_ + descentScore S A tail a
      rw [symmetricScore_opposite S, scoreBase_reverse S, ih a]

theorem descentScore_lt_pow (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat}
    (chain : DescentChain S (IsVisibleGate S A) J K n)
    {i j : ι} (a : S.Atom i j) :
    descentScore S A chain a < (scoreBase S i j)^n := by
  induction chain with
  | nil J =>
      simp [descentScore]
  | @cons J K L n R hstrict tail ih =>
      change symmetricScore S (stageFilter S A R) a * (scoreBase S i j)^n +
          descentScore S A tail a < (scoreBase S i j)^(n+1)
      have hw := symmetricScore_lt_base S (stageFilter S A R) a
      calc
        _ < symmetricScore S (stageFilter S A R) a * (scoreBase S i j)^n +
              (scoreBase S i j)^n := Nat.add_lt_add_left ih _
        _ = (symmetricScore S (stageFilter S A R) a + 1) *
              (scoreBase S i j)^n := by simp [add_mul]
        _ ≤ (scoreBase S i j) * (scoreBase S i j)^n :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hw)
        _ = (scoreBase S i j)^(n+1) := by simp [pow_succ, Nat.mul_comm]

end CCO.Selectors
