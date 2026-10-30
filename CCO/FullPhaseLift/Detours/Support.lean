import CCO.FullPhaseLift.Detours.BinaryPath
import CCO.FullPhaseLift.Full.Frozen
import Mathlib.Data.Fin.VecNotation

/-! B048 C16. The ONE signed full diagram model is used literally.
Every consecutive edge carries the complete induced old two-point truth,
including all negative, nullary and repeated-coordinate tuples. Chords,
the root pair and every support-at-least-three tuple stay UNSPECIFIED. -/
universe v w
namespace CCO.FullPhaseLift.Detours
open Canonical
variable {L : Signature} {M : Type v}

/-- The tuple's support lies inside ONE consecutive edge of the path.
This is support, not the arity of the relation symbol. -/
def OnEdge {n k : ℕ} (xs : Fin k → Fin (n+1)) : Prop :=
  ∃ e : Fin n, ∀ a, xs a = e.castSucc ∨ xs a = e.succ

def edgeVertex {n : ℕ} (e : Fin n) : Fin 2 → Fin (n+1) := ![e.castSucc,e.succ]

theorem edgeVertex_cases {n : ℕ} (e : Fin n) (k : Fin 2) :
    edgeVertex e k = e.castSucc ∨ edgeVertex e k = e.succ := by
  fin_cases k <;> simp [edgeVertex]

theorem edgeVertex_injective {n : ℕ} (e : Fin n) : Function.Injective (edgeVertex e) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · have hh := congrArg Fin.val h
    simp [edgeVertex] at hh
  · have hh := congrArg Fin.val h
    simp [edgeVertex] at hh
  · rfl

def edgeEmbedding {n : ℕ} (e : Fin n) : Fin 2 ↪ Fin (n+1) :=
  ⟨edgeVertex e,edgeVertex_injective e⟩

theorem onEdge_small {n k : ℕ} (xs : Fin k → Fin (n+1)) (h : OnEdge xs) :
    Full.SmallSupport xs := by
  obtain ⟨e,he⟩ := h
  intro i j k
  rcases he i with hi | hi <;> rcases he j with hj | hj <;> rcases he k with hk | hk <;>
    simp_all

theorem edge_tuple_onEdge {n k : ℕ} (e : Fin n) (xs : Fin k → Fin 2) :
    OnEdge (edgeVertex e ∘ xs) := ⟨e,fun a => edgeVertex_cases e (xs a)⟩

noncomputable def fullPath {n : ℕ} (U : BoolTable L M) (point : Fin (n+1) → M) :
    Full.Partial L (Fin (n+1)) := by
  classical
  exact fun r xs => if OnEdge xs then some (U r (point ∘ xs)) else none

theorem fullPath_edge {n : ℕ} (U : BoolTable L M) (point : Fin (n+1) → M)
    (e : Fin n) (r : Fin L.size) (xs : Fin (L.arity r) → Fin 2) :
    fullPath U point r (edgeVertex e ∘ xs) = some (U r (point ∘ edgeVertex e ∘ xs)) := by
  classical
  exact if_pos (edge_tuple_onEdge e xs)

theorem fullPath_realizes {n : ℕ} (U : BoolTable L M) (point : Fin (n+1) → M) :
    Full.Realizes U (fullPath U point) point := by
  classical
  intro r xs b hd
  change (if OnEdge xs then some (U r (point ∘ xs)) else none) = some b at hd
  split at hd
  · exact Option.some.inj hd
  · cases hd

theorem fullPath_consistent {n : ℕ} (U : BoolTable L M) (point : Fin (n+1) ↪ M) :
    Full.Consistent U (fullPath U point) := by
  intro k _ j
  refine ⟨j.trans point,?_⟩
  intro r xs b hb
  exact fullPath_realizes U point r (j ∘ xs) b hb

theorem fullPath_high_none {n : ℕ} (U : BoolTable L M) (point : Fin (n+1) → M)
    (r : Fin L.size) (xs : Fin (L.arity r) → Fin (n+1)) (hs : ¬Full.SmallSupport xs) :
    fullPath U point r xs = none := by
  classical
  exact if_neg (fun h => hs (onEdge_small xs h))

/-- Each path edge is a genuine complete INDUCED old factor. The same
single witness table supplies all signs, so overlapping unary/nullary
truth values agree automatically. -/
def edgeFactor {n : ℕ} (U : BoolTable L M) (point : Fin (n+1) ↪ M) (e : Fin n) :
    Full.FrozenFactor U (fullPath U point) where
  size := 2
  inclusion := edgeEmbedding e
  table := pullback U (point ∘ edgeVertex e)
  age := ⟨embeddingOf (point ∘ edgeVertex e) (point.injective.comp (edgeVertex_injective e))
    (fun _ _ => rfl)⟩
  agrees r xs := fullPath_edge U point e r xs

theorem fullPath_higherCovered {n : ℕ} (U : BoolTable L M) (point : Fin (n+1) ↪ M) :
    Full.HigherCovered (edgeFactor U point) := by
  intro r xs b hd hs
  rw [fullPath_high_none U point r xs hs] at hd
  cases hd

theorem onEdge_no_root_pair {n k : ℕ} (hn : 2 ≤ n) (xs : Fin k → Fin (n+1))
    (hx : ∃ a, xs a = 0) (hy : ∃ b, xs b = Fin.last n) : ¬OnEdge xs := by
  rintro ⟨e,he⟩
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  have he0 : e.val = 0 ∨ e.val+1 = 0 := by
    rcases he a with h | h
    · exact Or.inl (congrArg Fin.val (h.symm.trans ha))
    · exact Or.inr (congrArg Fin.val (h.symm.trans ha))
  have hen : e.val = n ∨ e.val+1 = n := by
    rcases he b with h | h
    · exact Or.inl (congrArg Fin.val (h.symm.trans hb))
    · exact Or.inr (congrArg Fin.val (h.symm.trans hb))
  omega

/-- Every old tuple genuinely using BOTH roots is absent. Unary data at
each root stay present in its incident complete edge. -/
theorem fullPath_root_pair_none {n : ℕ} (U : BoolTable L M) (point : Fin (n+1) → M)
    (hn : 2 ≤ n) (r : Fin L.size) (xs : Fin (L.arity r) → Fin (n+1))
    (hx : ∃ a, xs a = 0) (hy : ∃ b, xs b = Fin.last n) : fullPath U point r xs = none := by
  classical
  exact if_neg (onEdge_no_root_pair hn xs hx hy)

end CCO.FullPhaseLift.Detours
