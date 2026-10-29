import CCO.ProfileHelly.Network
import Mathlib.Tactic.FinCases

/-! The optional source atomic fork premise has an ACTUAL three-distinct-
vertex witness in the FULL table class. No SAP or Helly is used here. -/
universe u v
namespace CCO.ProfileHelly
variable {ι : Type u} {T : Table.{u,v} ι}

def forkSort (i j k : ι) : Fin 3 → ι
  | ⟨0,_⟩ => i
  | ⟨1,_⟩ => j
  | ⟨_+2,_⟩ => k

def forkEdge {i j k : ι} (a : T.Atom i j) (b : T.Atom i k) (c : T.Atom j k) :
    (p q : Fin 3) → Option (T.Atom (forkSort i j k p) (forkSort i j k q))
  | ⟨0,_⟩,⟨0,_⟩ => none
  | ⟨0,_⟩,⟨1,_⟩ => some a
  | ⟨0,_⟩,⟨_+2,_⟩ => some b
  | ⟨1,_⟩,⟨0,_⟩ => some (T.conv a)
  | ⟨1,_⟩,⟨1,_⟩ => none
  | ⟨1,_⟩,⟨_+2,_⟩ => some c
  | ⟨_+2,_⟩,⟨0,_⟩ => some (T.conv b)
  | ⟨_+2,_⟩,⟨1,_⟩ => some (T.conv c)
  | ⟨_+2,_⟩,⟨_+2,_⟩ => none

def forkNetwork {i j k : ι} (a : T.Atom i j) (b : T.Atom i k) (c : T.Atom j k)
    (h : T.triangle a c b) : CompleteNetwork T (forkSort i j k) where
  edge := forkEdge a b c
  diagonal := by intro p; fin_cases p <;> rfl
  edge_reverse := by
    intro p q
    fin_cases p <;> fin_cases q <;> dsimp [forkEdge,forkSort]
    all_goals first | rfl | exact congrArg some (T.conv_invol _)
  complete := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> dsimp [forkEdge,forkSort] at *
    all_goals first | exact False.elim (hpq rfl) | exact ⟨_,rfl⟩
  legal := by
    have h021 := (T.peirce_left a c b).mp h
    have h102 := (T.peirce_right a c b).mp h
    have h120 := (T.peirce_left (T.conv a) b c).mp h102
    have h201 := (T.peirce_right b (T.conv c) a).mp h021
    have h210 := (T.reverse a c b).mp h
    intro p q r hpq hqr hpr a' b' c' ha hb hc
    fin_cases p <;> fin_cases q <;> fin_cases r <;> dsimp [forkEdge,forkSort] at * <;> simp_all
    all_goals
      have h1 := Option.some.inj ha
      have h2 := Option.some.inj hb
      have h3 := Option.some.inj hc
      cases h1
      cases h2
      cases h3
      assumption

/-- C35: the incident fork has THREE distinct FORMAL vertices, even when
its sorts repeat. FULL triangle-defined membership is built explicitly. -/
theorem distinct_fork (laws : TableLaws T) {i j k : ι} (a : T.Atom i j) (b : T.Atom i k) :
    ∃ N : CompleteNetwork T (forkSort i j k), N.edge 0 1 = some a ∧ N.edge 0 2 = some b := by
  obtain ⟨c,hc⟩ := laws.total (T.conv a) b
  have ht : T.triangle a c b := by
    simpa only [T.conv_invol] using (T.peirce_right (T.conv a) b c).mp
      ((T.product_singleton _ _ _).mp hc)
  exact ⟨forkNetwork a b c ht,rfl,rfl⟩

end CCO.ProfileHelly
