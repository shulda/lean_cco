import CCO.StrongExact.CycleCompletion
import CCO.StrongGeometry

/-!
# Finite, typed, off-diagonal STRONG path-consistency networks

Only ordered pairs of *distinct formal vertices* have domains. The domains
are Boolean subsets of the actual diversity atom palettes and may become
empty during pruning. No equality or RAW represented-relation identities
are introduced. The source PC fixed point is obtained by iteration of this
monotone and deflationary operation.
-/

universe u v w

namespace CCO

/-- The domain of a strong PC network consists of precisely the ordered
distinct formal pairs; a diagonal pair has no network menu. -/
structure DistinctPair (V : Type w) where
  src : V
  dst : V
  ne : src ≠ dst

namespace StrongPC

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource ι X} {V : Type w}
variable (D : PartialDiagram S V)

/-- A typed Boolean menu for every ordered distinct pair. -/
abbrev Network :=
  ∀ p : DistinctPair V, S.Menu (D.vertexSort p.src) (D.vertexSort p.dst)

/-- Pointwise refinement of networks. -/
def Refines (A B : Network D) : Prop := ∀ p, A p ⊆ B p

/-- C10: One synchronous STRONG PC update. The support vertex is
distinct from both endpoints, even if its named sort repeats theirs. -/
def step (N : Network D) : Network D := fun p =>
  N p ∩ {a | ∀ z : V, (hxz : p.src ≠ z) → (hzy : z ≠ p.dst) →
    a ∈ S.product (N ⟨p.src, z, hxz⟩) (N ⟨z, p.dst, hzy⟩)}

/-- Actual specified singleton domains, with typed Top on missing edges. -/
def initial : Network D := fun p =>
  match D.edge p.src p.dst p.ne with
  | none => Set.univ
  | some a => {a}

/-- A literal finite number of synchronous Boolean PC updates. -/
def iterate (N : Network D) : Nat → Network D
  | 0 => N
  | n + 1 => step D (iterate N n)

/-- A stable network is fixed by all distinct-middle-vertex constraints. -/
def Stable (N : Network D) : Prop := ∀ p, step D N p = N p

theorem step_refines (N : Network D) : Refines D (step D N) N := by
  intro p a ha
  exact ha.1

/-- Monotonicity is valid even for empty intermediate Boolean menus. -/
theorem step_monotone {M N : Network D} (h : Refines D M N) :
    Refines D (step D M) (step D N) := by
  intro p a ha
  refine ⟨h p ha.1, ?_⟩
  intro z hxz hzy
  exact S.product_mono (h ⟨p.src, z, hxz⟩)
    (h ⟨z, p.dst, hzy⟩) (ha.2 z hxz hzy)

/-- Every finite step loses only domains, never introduces a new atom. -/
theorem iterate_succ_refines (N : Network D) (n : Nat) :
    Refines D (iterate D N (n + 1)) (iterate D N n) := by
  exact step_refines D (iterate D N n)

theorem iterate_monotone {M N : Network D} (h : Refines D M N)
    (n : Nat) : Refines D (iterate D M n) (iterate D N n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact step_monotone D ih

/-- C10 greatestness: every stable refinement of the initial network is
contained in EVERY iterate. This is the induction required when the
finite descending chain is later identified with its stationary value. -/
theorem stable_refines_iterate (M N : Network D)
    (hStable : Stable D M) (hMN : Refines D M N)
    (n : Nat) : Refines D M (iterate D N n) := by
  induction n with
  | zero => exact hMN
  | succ n ih =>
      intro p a ha
      have hFix : a ∈ step D M p := by
        rw [hStable p]
        exact ha
      exact step_monotone D ih p hFix

/-- Atomic colours of every pair in one actual injective realization
belong to the displayed network domains. -/
def SupportsCompletion (N : Network D) (f : DiagramHom D) : Prop :=
  ∀ (p : DistinctPair V)
    (a : S.Atom (D.vertexSort p.src) (D.vertexSort p.dst)),
    S.colour (f.point p.src) (f.point p.dst) = some a → a ∈ N p

theorem supports_initial (f : DiagramHom D) :
    SupportsCompletion D (initial D) f := by
  intro p a ha
  cases he : D.edge p.src p.dst p.ne with
  | none =>
      simp [initial, he]
  | some b =>
      have hb : S.colour (f.point p.src) (f.point p.dst) = some b :=
        f.preserves_edge p.src p.dst p.ne b he
      have hab : a = b := Option.some.inj (ha.symm.trans hb)
      simp [initial, he, hab]

/-- C10 survivor induction step. A genuine injective realization
supplies a THREE-DISTINCT-REAL-POINT triangle through every third
formal vertex, so its actual atom never gets pruned. -/
theorem supports_step (N : Network D) (f : DiagramHom D)
    (hf : f.IsInjective) (hN : SupportsCompletion D N f) :
    SupportsCompletion D (step D N) f := by
  intro p a ha
  refine ⟨hN p a ha, ?_⟩
  intro z hxz hzy
  have hXZ : f.image p.src ≠ f.image z := by
    intro he
    exact hxz (hf he)
  have hZY : f.image z ≠ f.image p.dst := by
    intro he
    exact hzy (hf he)
  obtain ⟨b, hb⟩ := S.some_colour_of_ne
    (f.point p.src) (f.point z) hXZ
  obtain ⟨c, hc⟩ := S.some_colour_of_ne
    (f.point z) (f.point p.dst) hZY
  exact ⟨b, hN ⟨p.src, z, hxz⟩ b hb,
    c, hN ⟨z, p.dst, hzy⟩ c hc,
    ⟨f.point p.src, f.point z, f.point p.dst, hb, hc, ha⟩⟩

/-- No actual injective completion atom is ever lost by finite PC
iteration, including paths with repeated *sorts* (not vertices). -/
theorem supports_all_iterates (f : DiagramHom D)
    (hf : f.IsInjective) (n : Nat) :
    SupportsCompletion D (iterate D (initial D) n) f := by
  induction n with
  | zero => exact supports_initial D f
  | succ n ih => exact supports_step D _ f hf ih

end StrongPC
end CCO
