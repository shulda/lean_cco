import CCO.RawExact.JointExactRequests
import Mathlib.Logic.Function.Basic

/-!
# Finite joint orbital partial isomorphisms and one-point extension

The finite domain consists of actual tagged quotient values. The map
retains each named sort and preserves the complete actual pair orbitals.
This already forces injection. With full-exact kernels, C13 extends it
by an arbitrary displayed quotient point, including an original real
point when the displayed quotient map is the identity.
-/

universe u v w z q t

namespace CCO.RawExact

/-- A finite partial isomorphism in the complete actual joint orbital
language. Values of `send` outside the finite domain are immaterial. -/
structure FiniteJointPartialIso (G : Type t) {K : Type z}
    (Q : K → Type q) [Group G] [∀ k, MulAction G (Q k)] where
  domain : Finset (Sigma Q)
  send : ∀ p : Sigma Q, Q p.1
  preserves : ∀ p q, p ∈ domain → q ∈ domain →
    GroupActions.orbital (G := G) p.2 q.2 (send p) (send q)

namespace FiniteJointPartialIso

variable {G : Type t} [Group G] {K : Type z} {Q : K → Type q}
variable [∀ k, MulAction G (Q k)]

/-- The partial map's output is in the same literal named sort. -/
def image (f : FiniteJointPartialIso G Q) (p : Sigma Q) : Sigma Q :=
  ⟨p.1, f.send p⟩

/-- Complete named orbitals are retained as relations, rather than only
one chosen atomic constraint at each displayed pair. -/
theorem preserves_named_orbitals (f : FiniteJointPartialIso G Q)
    (p q : Sigma Q) (hp : p ∈ f.domain) (hq : q ∈ f.domain) :
    GroupActions.orbital (G := G) p.2 q.2 =
      GroupActions.orbital (G := G) (f.send p) (f.send q) :=
  GroupActions.orbital_eq_of_mem p.2 q.2 (f.send p) (f.send q)
    (f.preserves p q hp hq)

/-- Logical equality orbitals force actual injection on the displayed
domain. No freshness or SAP premise is used. -/
theorem injOn_image (f : FiniteJointPartialIso G Q) :
    Set.InjOn f.image (↑f.domain : Set (Sigma Q)) := by
  intro p hp q hq hpq
  obtain ⟨g, hgp, hgq⟩ := f.preserves p q hp hq
  have hgp' : g • p = f.image p := by
    cases p with
    | mk k p =>
        change (⟨k, g • p⟩ : Sigma Q) = ⟨k, f.send ⟨k, p⟩⟩
        exact congrArg (Sigma.mk k) hgp
  have hgq' : g • q = f.image q := by
    cases q with
    | mk k q =>
        change (⟨k, g • q⟩ : Sigma Q) = ⟨k, f.send ⟨k, q⟩⟩
        exact congrArg (Sigma.mk k) hgq
  have hEq : g • p = g • q := hgp'.trans (hpq.trans hgq'.symm)
  have hInv := congrArg (fun a : Sigma Q => g⁻¹ • a) hEq
  simpa only [inv_smul_smul] using hInv

end FiniteJointPartialIso

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Actual finite joint one-point extension. The designated point may
be an original real point (identity quotient) or any actual exact
quotient point. C13 remains visible until its source proof is supplied. -/
theorem finite_joint_extension_of_exact_ball_helly
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S)
    {K : Type z} (Q : K → Type q) [∀ k, MulAction G (Q k)]
    (root : K → ι) (π : ∀ k, X (root k) → Q k)
    (ontoπ : ∀ k, Function.Surjective (π k))
    (equivπ : ∀ k (g : G) c, π k (g • c) = g • π k c)
    (E : ∀ k, NonemptyExact S (root k) (root k))
    (hE : ∀ k, GroupActions.kernel (π k) = evaluate S (E k).words)
    (f : FiniteJointPartialIso G Q) (k : K) (x : X (root k)) :
    ∃ f' : FiniteJointPartialIso G Q,
      (∀ p, p ∈ f'.domain ↔ p = (⟨k, π k x⟩ : Sigma Q) ∨ p ∈ f.domain) ∧
      ∀ p ∈ f.domain, f'.send p = f.send p := by
  classical
  let a : Sigma Q := ⟨k, π k x⟩
  by_cases ha : a ∈ f.domain
  · refine ⟨f, ?_, ?_⟩
    · intro p
      constructor
      · exact fun hp => Or.inr hp
      · rintro (rfl | hp)
        · exact ha
        · exact hp
    · intro p hp
      rfl
  let I := ↥f.domain
  let sort : I → ι := fun p => root p.val.1
  let Q' : I → Type q := fun p => Q p.val.1
  let π' : ∀ p : I, X (sort p) → Q' p := fun p => π p.val.1
  let source : ∀ p : I, Q' p := fun p => p.val.2
  let target : ∀ p : I, Q' p := fun p => f.send p.val
  have hPairs : ∀ p q : I,
      GroupActions.orbital (G := G)
        (source p) (source q) (target p) (target q) :=
    fun p q => f.preserves p.val q.val p.property q.property
  obtain ⟨y, hy⟩ := joint_real_point_requests_of_exact_kernels S H hHelly
    sort Q' π' (fun p => ontoπ p.val.1) (fun p => equivπ p.val.1)
    (fun p => E p.val.1) (fun p => hE p.val.1)
    x source target hPairs
  have hNew : ∀ p ∈ f.domain,
      GroupActions.orbital (G := G) (π k x) p.2 (π k y) (f.send p) := by
    intro p hp
    obtain ⟨g, hgx, hgp⟩ := hy ⟨p, hp⟩
    refine ⟨g, ?_, hgp⟩
    calc
      g • π k x = π k (g • x) := (equivπ k g x).symm
      _ = π k y := congrArg (π k) hgx
  have hSelf : GroupActions.orbital (G := G)
      (π k x) (π k x) (π k y) (π k y) := by
    obtain ⟨g, hg⟩ := S.original_sort_transitive_of_homogeneous H (root k) x y
    have hπ : g • π k x = π k y := by
      rw [← equivπ, hg]
    exact ⟨g, hπ, hπ⟩
  let send' : ∀ p : Sigma Q, Q p.1 := Function.update f.send a (π k y)
  have hOld : ∀ p ∈ f.domain, send' p = f.send p := by
    intro p hp
    have hpa : p ≠ a := by
      intro heq
      exact ha (heq ▸ hp)
    exact Function.update_of_ne hpa _ _
  have hPreserves : ∀ p q,
      p ∈ insert a f.domain → q ∈ insert a f.domain →
      GroupActions.orbital (G := G) p.2 q.2 (send' p) (send' q) := by
    intro p q hp hq
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · simpa only [send', Function.update_self, a] using hSelf
      · rw [hOld q hq]
        simpa only [send', Function.update_self, a] using hNew q hq
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · rw [hOld p hp]
        obtain ⟨g, hgnew, hgp⟩ := hNew p hp
        refine ⟨g, hgp, ?_⟩
        simpa only [send', Function.update_self, a] using hgnew
      · rw [hOld p hp, hOld q hq]
        exact f.preserves p q hp hq
  refine ⟨⟨insert a f.domain, send', hPreserves⟩, ?_, hOld⟩
  intro p
  exact Finset.mem_insert

end CCO.RawExact
