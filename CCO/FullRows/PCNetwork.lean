import CCO.StrongExact.PCConverse
import CCO.StrongExact.PCSoundness
import CCO.StrongExact.PCExactness

/-! Fair, converse-paired oriented PC pruning.  A legal atomic assignment
need not arise from a global realization.  All Boolean menus, including
empty ones, participate in the finite termination argument. -/

universe u v w z
namespace CCO.FullRows
open StrongPC

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

abbrev AtomicAssignment := ∀ p : DistinctPair V,
  S.Atom (D.vertexSort p.src) (D.vertexSort p.dst)

def LegalAssignment (a : AtomicAssignment D) : Prop :=
  ∀ x y z (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z),
    S.Triangle (a ⟨x,y,hxy⟩) (a ⟨y,z,hyz⟩) (a ⟨x,z,hxz⟩)

def Survives (N : Network D) (a : AtomicAssignment D) : Prop :=
  ∀ p, a p ∈ N p

theorem survives_step (N : Network D) (a : AtomicAssignment D)
    (ha : LegalAssignment D a) (hN : Survives D N a) :
    Survives D (step D N) a := by
  intro p
  refine ⟨hN p, ?_⟩
  intro y hxy hyz
  exact ⟨a ⟨p.src,y,hxy⟩, hN _, a ⟨y,p.dst,hyz⟩, hN _,
    ha p.src y p.dst hxy hyz p.ne⟩

theorem survives_iterate (N : Network D) (a : AtomicAssignment D)
    (ha : LegalAssignment D a) (hN : Survives D N a) (n : Nat) :
    Survives D (iterate D N n) a := by
  induction n with
  | zero => exact hN
  | succ n ih => exact survives_step D _ a ha ih

/-- One output pair with its distinct support vertex.  Its reverse output
is pruned at the same time, so converse symmetry is maintained. -/
structure Constraint (V : Type z) where
  pair : DistinctPair V
  middle : V
  left_ne : pair.src ≠ middle
  right_ne : middle ≠ pair.dst

namespace Constraint
def Applies (c : Constraint V) (p : DistinctPair V) : Prop :=
  (p.src = c.pair.src ∧ p.dst = c.pair.dst) ∨
  (p.src = c.pair.dst ∧ p.dst = c.pair.src)

theorem applies_reverse (c : Constraint V) (p : DistinctPair V) :
    c.Applies ⟨p.dst,p.src,p.ne.symm⟩ ↔ c.Applies p := by
  simp only [Applies]
  tauto
end Constraint

/-- The two oriented output constraints use the same old network. -/
def prune (c : Constraint V) (N : Network D) : Network D := fun p =>
  N p ∩ {a | c.Applies p → ∀ (hx : p.src ≠ c.middle) (hy : c.middle ≠ p.dst),
    a ∈ S.product (N ⟨p.src,c.middle,hx⟩) (N ⟨c.middle,p.dst,hy⟩)}

theorem prune_refines (c : Constraint V) (N : Network D) :
    Refines D (prune D c N) N := fun _ _ h => h.1

theorem prune_monotone (c : Constraint V) {M N : Network D}
    (h : Refines D M N) : Refines D (prune D c M) (prune D c N) := by
  intro p a ha
  refine ⟨h p ha.1, ?_⟩
  intro hp hx hy
  exact S.product_mono (h _) (h _) (ha.2 hp hx hy)

theorem survives_prune (c : Constraint V) (N : Network D)
    (a : AtomicAssignment D) (ha : LegalAssignment D a) (hN : Survives D N a) :
    Survives D (prune D c N) a := by
  intro p
  refine ⟨hN p, ?_⟩
  intro _ hx hy
  exact ⟨a ⟨p.src,c.middle,hx⟩, hN _, a ⟨c.middle,p.dst,hy⟩, hN _,
    ha p.src c.middle p.dst hx hy p.ne⟩

private theorem prune_converse_half (c : Constraint V) (N : Network D)
    (hConv : ConverseClosed D N) (p : DistinctPair V) :
    prune D c N ⟨p.dst,p.src,p.ne.symm⟩ ⊆ S.opposite (prune D c N p) := by
  intro a ha
  change S.conv a ∈ prune D c N p
  refine ⟨?_, ?_⟩
  · have h := ha.1
    rw [hConv p] at h
    exact h
  · intro hp hx hy
    have hprod := ha.2 ((c.applies_reverse p).mpr hp) hy.symm hx.symm
    have hOpp : S.conv a ∈ S.opposite
        (S.product (N ⟨p.dst,c.middle,hy.symm⟩) (N ⟨c.middle,p.src,hx.symm⟩)) := by
      change S.conv (S.conv a) ∈ S.product
        (N ⟨p.dst,c.middle,hy.symm⟩) (N ⟨c.middle,p.src,hx.symm⟩)
      simpa only [S.conv_invol] using hprod
    rw [S.product_opposite] at hOpp
    rw [← hConv ⟨c.middle,p.src,hx.symm⟩,
      ← hConv ⟨p.dst,c.middle,hy.symm⟩] at hOpp
    exact hOpp

theorem prune_converse (c : Constraint V) (N : Network D)
    (hConv : ConverseClosed D N) : ConverseClosed D (prune D c N) := by
  intro p
  apply Set.Subset.antisymm
  · exact prune_converse_half D c N hConv p
  · intro a ha
    have hb := prune_converse_half D c N hConv ⟨p.dst,p.src,p.ne.symm⟩ ha
    change S.conv (S.conv a) ∈ prune D c N ⟨p.dst,p.src,p.ne.symm⟩ at hb
    simpa only [S.conv_invol] using hb

theorem stable_prune (N : Network D) (hN : Stable D N) (c : Constraint V) :
    prune D c N = N := by
  funext p
  apply Set.Subset.antisymm (prune_refines D c N p)
  intro a ha
  refine ⟨ha, ?_⟩
  intro _ hx hy
  exact stable_triangle_support D N hN hx hy p.ne ha

theorem stable_iff_all_prune (N : Network D) :
    Stable D N ↔ ∀ c : Constraint V, prune D c N = N := by
  constructor
  · exact stable_prune D N
  · intro h p
    apply Set.Subset.antisymm (step_refines D N p)
    intro a ha
    refine ⟨ha, ?_⟩
    intro y hx hy
    let c : Constraint V := ⟨p,y,hx,hy⟩
    have hb : a ∈ prune D c N p := by rw [h c]; exact ha
    exact hb.2 (Or.inl ⟨rfl,rfl⟩) hx hy

/-- `none` permits an idle step and makes the definition cover vertex sets
with no triples. Fairness requires every actual oriented constraint later. -/
def scheduledStep (c : Option (Constraint V)) (N : Network D) : Network D :=
  match c with
  | none => N
  | some c => prune D c N

def trajectory (N : Network D) (schedule : Nat → Option (Constraint V)) : Nat → Network D
  | 0 => N
  | n + 1 => scheduledStep D (schedule n) (trajectory N schedule n)

def Fair (schedule : Nat → Option (Constraint V)) : Prop :=
  ∀ c n, ∃ m, n ≤ m ∧ schedule m = some c

theorem scheduledStep_refines (c : Option (Constraint V)) (N : Network D) :
    Refines D (scheduledStep D c N) N := by
  cases c with
  | none => exact fun _ _ h => h
  | some c => exact prune_refines D c N

theorem trajectory_antitone (N : Network D) (schedule : Nat → Option (Constraint V)) :
    Antitone (trajectory D N schedule) := by
  apply antitone_nat_of_succ_le
  intro n
  exact scheduledStep_refines D (schedule n) _

theorem trajectory_refines_initial (N : Network D)
    (schedule : Nat → Option (Constraint V)) (n : Nat) :
    Refines D (trajectory D N schedule n) N :=
  trajectory_antitone D N schedule (Nat.zero_le n)

theorem stable_refines_trajectory (M N : Network D) (hM : Stable D M)
    (hMN : Refines D M N) (schedule : Nat → Option (Constraint V)) (n : Nat) :
    Refines D M (trajectory D N schedule n) := by
  induction n with
  | zero => exact hMN
  | succ n ih =>
      change Refines D M (scheduledStep D (schedule n) _)
      cases hc : schedule n with
      | none => exact ih
      | some c =>
          change Refines D M (prune D c _)
          rw [← stable_prune D M hM c]
          exact prune_monotone D c ih

theorem survives_trajectory (N : Network D) (a : AtomicAssignment D)
    (ha : LegalAssignment D a) (hN : Survives D N a)
    (schedule : Nat → Option (Constraint V)) (n : Nat) :
    Survives D (trajectory D N schedule n) a := by
  induction n with
  | zero => exact hN
  | succ n ih =>
      change Survives D (scheduledStep D (schedule n) _) a
      cases schedule n with
      | none => exact ih
      | some c => exact survives_prune D c _ a ha ih

theorem trajectory_converse (N : Network D) (hN : ConverseClosed D N)
    (schedule : Nat → Option (Constraint V)) (n : Nat) :
    ConverseClosed D (trajectory D N schedule n) := by
  induction n with
  | zero => exact hN
  | succ n ih =>
      change ConverseClosed D (scheduledStep D (schedule n) _)
      cases schedule n with
      | none => exact ih
      | some c => exact prune_converse D c _ ih

/-- Every fair order terminates, and the limit is greatest among all
stable refinements of the initial Boolean network. -/
theorem fair_stabilizes (N : Network D) (schedule : Nat → Option (Constraint V))
    (hFair : Fair schedule) :
    ∃ n, Stable D (trajectory D N schedule n) ∧
      (∀ m, n ≤ m → trajectory D N schedule m = trajectory D N schedule n) ∧
      (∀ M, Stable D M → Refines D M N → Refines D M (trajectory D N schedule n)) := by
  classical
  let : Finite (Network D) := finite_network D
  obtain ⟨n, hn⟩ := WellFoundedLT.antitone_chain_condition (trajectory_antitone D N schedule)
  have hConst : ∀ m, n ≤ m → trajectory D N schedule m = trajectory D N schedule n :=
    fun m hm => (hn m hm).symm
  refine ⟨n, ?_, hConst, ?_⟩
  · apply (stable_iff_all_prune D _).mpr
    intro c
    obtain ⟨m, hm, hmc⟩ := hFair c n
    have heq := hConst (m+1) (hm.trans (Nat.le_succ m))
    change scheduledStep D (schedule m) (trajectory D N schedule m) = _ at heq
    rw [hmc, hConst m hm] at heq
    exact heq
  · intro M hM hMN
    exact stable_refines_trajectory D M N hM hMN schedule n

/-- Specializing the arbitrary-initial-network result gives precisely
StrongPC's existing canonical greatest network, regardless of fair order. -/
theorem fair_limit_fixedNetwork (schedule : Nat → Option (Constraint V))
    (hFair : Fair schedule) :
    ∃ n, ∀ m, n ≤ m → trajectory D (initial D) schedule m = fixedNetwork D := by
  obtain ⟨n, hStable, hConst, hGreatest⟩ := fair_stabilizes D (initial D) schedule hFair
  have heq : trajectory D (initial D) schedule n = fixedNetwork D := by
    apply le_antisymm
    · exact fixedNetwork_greatest D _ hStable (trajectory_refines_initial D _ schedule n)
    · exact hGreatest _ (fixedNetwork_stable D) (fixedNetwork_refines_initial D)
  exact ⟨n, fun m hm => (hConst m hm).trans heq⟩

/-- Fair update orders have the same limit for every starting network,
not merely the singleton/top network attached to a diagram. -/
theorem fair_limits_equal (N : Network D)
    (schedule₁ schedule₂ : Nat → Option (Constraint V))
    (h₁ : Fair schedule₁) (h₂ : Fair schedule₂) :
    ∃ n m, (∀ k, n ≤ k → trajectory D N schedule₁ k = trajectory D N schedule₁ n) ∧
      (∀ k, m ≤ k → trajectory D N schedule₂ k = trajectory D N schedule₂ m) ∧
      trajectory D N schedule₁ n = trajectory D N schedule₂ m := by
  obtain ⟨n, hn, hc₁, hg₁⟩ := fair_stabilizes D N schedule₁ h₁
  obtain ⟨m, hm, hc₂, hg₂⟩ := fair_stabilizes D N schedule₂ h₂
  refine ⟨n,m,hc₁,hc₂,le_antisymm ?_ ?_⟩
  · exact hg₂ _ hn (trajectory_refines_initial D N schedule₁ n)
  · exact hg₁ _ hm (trajectory_refines_initial D N schedule₂ m)

/-- The actual completion is used only to prove nonemptiness. Original
exactness follows from the already proved source SAP/CCO calculus. -/
structure PCCompletionData : Prop where
  nonempty : ∀ p : DistinctPair V, (fixedNetwork D p).Nonempty
  exact : ∀ p : DistinctPair V, StrongExact.Exact S (fixedNetwork D p)
  pc : ∀ x y z (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z),
    S.PC (fixedNetwork D ⟨x,y,hxy⟩) (fixedNetwork D ⟨y,z,hyz⟩) (fixedNetwork D ⟨x,z,hxz⟩)
  specified : ∀ x y (hxy : x ≠ y) (a : S.Atom (D.vertexSort x) (D.vertexSort y)),
    D.edge x y hxy = some a → fixedNetwork D ⟨x,y,hxy⟩ = {a}

theorem pcCompletionData_of_strongCompletion
    {G : Type*} [Group G] [∀ i, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) (hD : D.HasStrongCompletion) : PCCompletionData D := by
  obtain ⟨f,hf⟩ := hD
  have hn := fixedNetwork_nonempty_of_completion D f hf
  exact {
    nonempty := hn
    exact := fixedNetwork_exact_of_nonempty D H sap cco hn
    pc := fun _ _ _ hxy hyz hxz => fixedNetwork_PC D hxy hyz hxz
    specified := fun _ _ hxy a ha =>
      fixedNetwork_eq_specified_singleton_of_nonempty D hxy a ha (hn _) }

end CCO.FullRows
