import CCO.RawExact.Distribution
import CCO.RawExact.ExactSaturations

/-!
# B002 C10: genuine two-sided nonempty exact saturation distribution

For a finite list of nonempty full-exact typed relations with an
ACTUALLY nonempty meet, E;(meet Dᵢ);K = meet (E;Dᵢ;K).
The left and right factors are separately represented nonempty exact
relations, not arbitrary invariant supports. The proof invokes
C10's exact one-sided distribution TWICE and verifies nonemptiness
of the intermediate meet using actual original-sort transitivity.

The only outstanding source-level provider is C13 exact-ball Helly,
which is kept as an explicit argument; this is not a fake general
distributive law for empty intersections.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

theorem fullExact_saturation_meet_distribution
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S)
    {i j : ι}
    (E : NonemptyExact S i i) (K : NonemptyExact S j j)
    (D : List (NonemptyExact S i j))
    (hD : TRel.Nonempty
      (fun x y => ∀ d, d ∈ D → evaluate S d.words x y)) :
    saturate (evaluate S E.words)
        (fun x y => ∀ d, d ∈ D → evaluate S d.words x y)
        (evaluate S K.words) =
      (fun x z => ∀ d, d ∈ D →
        saturate (evaluate S E.words) (evaluate S d.words)
          (evaluate S K.words) x z) := by
  let M := exactFamilyMeet S D hD
  let P : List (NonemptyExact S i j) :=
    D.map (fun d => convolutionExact S H E d)
  have hPfamily :
      (fun x y => ∀ p, p ∈ P → evaluate S p.words x y) =
      (fun x y => ∀ d, d ∈ D →
        TRel.comp (evaluate S E.words) (evaluate S d.words) x y) := by
    funext x y
    apply propext
    constructor
    · intro h d hd
      have hp : convolutionExact S H E d ∈ P :=
        List.mem_map.mpr ⟨d, hd, rfl⟩
      have hword := h (convolutionExact S H E d) hp
      rw [convolutionExact_represents S H hHelly E d] at hword
      exact hword
    · intro h p hp
      obtain ⟨d, hd, hpEq⟩ := List.mem_map.mp hp
      subst p
      rw [convolutionExact_represents S H hHelly E d]
      exact h d hd
  have hLeft := comp_exact_meet_right S H hHelly E D hD
  have hP : TRel.Nonempty
      (fun x y => ∀ p, p ∈ P → evaluate S p.words x y) := by
    have hp := S.raw_nonempty_comp_of_homogeneous H
      (evaluate S E.words) (evaluate S M.words)
      E.nonempty M.nonempty
      (presentation_invariant_of_homogeneous S H M.words)
    rw [exactFamilyMeet_relation S D hD] at hp
    rw [hLeft] at hp
    rw [← hPfamily] at hp
    exact hp
  have hRight := comp_exact_meet_left S H hHelly P hP K
  calc
    saturate (evaluate S E.words)
        (fun x y => ∀ d, d ∈ D → evaluate S d.words x y)
        (evaluate S K.words) =
      TRel.comp
        (fun x y => ∀ p, p ∈ P → evaluate S p.words x y)
        (evaluate S K.words) := by
          unfold saturate
          rw [hPfamily, ← hLeft]
    _ = (fun x z => ∀ p, p ∈ P →
          TRel.comp (evaluate S p.words) (evaluate S K.words) x z) :=
      hRight
    _ = (fun x z => ∀ d, d ∈ D →
          saturate (evaluate S E.words) (evaluate S d.words)
            (evaluate S K.words) x z) := by
      funext x z
      apply propext
      constructor
      · intro h d hd
        have hp : convolutionExact S H E d ∈ P :=
          List.mem_map.mpr ⟨d, hd, rfl⟩
        have hactual := h (convolutionExact S H E d) hp
        rw [convolutionExact_represents S H hHelly E d] at hactual
        exact hactual
      · intro h p hp
        obtain ⟨d, hd, hpEq⟩ := List.mem_map.mp hp
        subst p
        rw [convolutionExact_represents S H hHelly E d]
        exact h d hd

end CCO.RawExact
