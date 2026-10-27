import CCO.PositiveWords
import CCO.StrongExact.PCNetwork

/-!
# Original finite-meet STRONG exact menus

An exact menu is a NONEMPTY evaluated finite intersection of profiles
of genuinely positive diversity words; the empty list means typed
diversity Top. The source's unital RAW family is deliberately excluded.

This module establishes the elementary, hypothesis-free presentation
calculus. Theta Helly (C07), convolution (C08), and canonical PC
domains (C13) are subsequent theorems, not implicit facts about
arbitrary intersections.
-/

universe u v w z

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, w} ι X)
variable {i j : ι}

/-- Evaluated intersection of finitely many genuinely positive word
profiles. The empty family imposes zero restrictions and gives Top. -/
def present (words : List (PositiveWord S i j)) : S.Menu i j :=
  {a | ∀ w ∈ words, a ∈ PositiveWord.profile S w}

/-- Original STRONG exact domain, with required nonempty evaluation. -/
def Exact (A : S.Menu i j) : Prop :=
  A.Nonempty ∧ ∃ words : List (PositiveWord S i j), A = present S words

theorem present_nil :
    present S ([] : List (PositiveWord S i j)) = Set.univ := by
  ext a
  simp [present]

theorem present_append
    (as bs : List (PositiveWord S i j)) :
    present S (as ++ bs) = present S as ∩ present S bs := by
  ext a
  simp [present, List.mem_append, forall_or]

theorem present_cons
    (w : PositiveWord S i j) (ws : List (PositiveWord S i j)) :
    present S (w :: ws) =
      PositiveWord.profile S w ∩ present S ws := by
  ext a
  simp [present, List.mem_cons, forall_or]

/-- Every actual atomic diversity singleton is exact, even when its
source and target sorts coincide; no identity colour is introduced. -/
theorem exact_singleton (a : S.Atom i j) :
    Exact S ({a} : S.Menu i j) := by
  refine ⟨⟨a, by simp⟩, ⟨[.single a], ?_⟩⟩
  ext b
  simp [present, PositiveWord.profile]

/-- Empty-list Top is exact if and only if its literal diversity
palette is nonempty. This condition is kept explicit because
AtomicSource alone does not assert a nonempty palette for each pair. -/
theorem exact_top (h : (Set.univ : S.Menu i j).Nonempty) :
    Exact S (Set.univ : S.Menu i j) :=
  ⟨h, ⟨[], (present_nil S).symm⟩⟩

/-- The finite intersection presentation is simply list concatenation.
We require the RESULT to be nonempty; intersections with empty
evaluation never enter the original exact family. -/
theorem exact_inter {A B : S.Menu i j}
    (hA : Exact S A) (hB : Exact S B)
    (hAB : (A ∩ B).Nonempty) :
    Exact S (A ∩ B) := by
  rcases hA with ⟨_, as, hAs⟩
  rcases hB with ⟨_, bs, hBs⟩
  refine ⟨hAB, ⟨as ++ bs, ?_⟩⟩
  rw [hAs, hBs]
  exact (present_append S as bs).symm

end CCO.StrongExact
