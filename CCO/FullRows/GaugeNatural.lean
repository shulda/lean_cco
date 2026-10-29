import CCO.FullRows.PCNetwork
import CCO.SafeReadings.IndependentGauge
import CCO.SafeReadings.PaletteRelabelling
import CCO.SafeReadings.TransversalEndpoint

/-! Greatest PC is natural under genuine equivalences of typed palettes
and triangle tables, also between different formal diagrams. -/

universe u v w z z' t r s
namespace CCO.FullRows
open StrongPC SafeReadings

variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} {W : Type z'}
variable (D : PartialDiagram S V) (E : PartialDiagram S W) (σ : V ≃ W)

abbrev pairEquiv : DistinctPair V ≃ DistinctPair W where
  toFun p := ⟨σ p.src, σ p.dst, fun h => p.ne (σ.injective h)⟩
  invFun p := ⟨σ.symm p.src, σ.symm p.dst, fun h => p.ne (σ.symm.injective h)⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

/-- Only actual atom equivalences and actual triangle/converse preservation
are required. Initial specified-edge covariance is a separate hypothesis. -/
structure PCTransport where
  atom : ∀ p : DistinctPair V,
    S.Atom (D.vertexSort p.src) (D.vertexSort p.dst) ≃
      S.Atom (E.vertexSort (σ p.src)) (E.vertexSort (σ p.dst))
  triangle : ∀ x y z (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (b : S.Atom (D.vertexSort y) (D.vertexSort z))
    (c : S.Atom (D.vertexSort x) (D.vertexSort z)),
    S.Triangle a b c ↔ S.Triangle
      (atom ⟨x,y,hxy⟩ a) (atom ⟨y,z,hyz⟩ b) (atom ⟨x,z,hxz⟩ c)
  converse : ∀ p (a : S.Atom (D.vertexSort p.src) (D.vertexSort p.dst)),
    atom ⟨p.dst,p.src,p.ne.symm⟩ (S.conv a) = S.conv (atom p a)

namespace PCTransport
variable {D E σ} (T : PCTransport D E σ)

noncomputable def networkEquiv : Network D ≃ Network E :=
  (pairEquiv σ).piCongr (fun p => Equiv.setCongr (T.atom p))

@[simp] theorem networkEquiv_apply (N : Network D) (p : DistinctPair V) :
    T.networkEquiv N (pairEquiv σ p) = T.atom p '' N p := by
  exact Equiv.piCongr_apply_apply _ _ _ _

noncomputable def networkIso : Network D ≃o Network E where
  toEquiv := T.networkEquiv
  map_rel_iff' := by
    intro M N
    constructor
    · intro h p a ha
      have hp := h (pairEquiv σ p)
      rw [T.networkEquiv_apply, T.networkEquiv_apply] at hp
      have hmem := hp (Set.mem_image_of_mem (T.atom p) ha)
      exact (T.atom p).injective.mem_set_image.mp hmem
    · intro h q
      obtain ⟨p,rfl⟩ := (pairEquiv σ).surjective q
      rw [T.networkEquiv_apply, T.networkEquiv_apply]
      exact Set.image_mono (h p)

@[simp] theorem networkIso_apply (N : Network D) (p : DistinctPair V) :
    T.networkIso N (pairEquiv σ p) = T.atom p '' N p := T.networkEquiv_apply N p

theorem product_iff (x y z : V) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (A : S.Menu (D.vertexSort x) (D.vertexSort y))
    (B : S.Menu (D.vertexSort y) (D.vertexSort z))
    (c : S.Atom (D.vertexSort x) (D.vertexSort z)) :
    T.atom ⟨x,z,hxz⟩ c ∈
      S.product (T.atom ⟨x,y,hxy⟩ '' A) (T.atom ⟨y,z,hyz⟩ '' B) ↔
    c ∈ S.product A B := by
  constructor
  · rintro ⟨_, ⟨a,ha,rfl⟩, _, ⟨b,hb,rfl⟩, ht⟩
    exact ⟨a,ha,b,hb,(T.triangle x y z hxy hyz hxz a b c).mpr ht⟩
  · rintro ⟨a,ha,b,hb,ht⟩
    exact ⟨_, ⟨a,ha,rfl⟩, _, ⟨b,hb,rfl⟩,
      (T.triangle x y z hxy hyz hxz a b c).mp ht⟩

theorem step_natural (N : Network D) :
    T.networkIso (step D N) = step E (T.networkIso N) := by
  funext q
  obtain ⟨p,rfl⟩ := (pairEquiv σ).surjective q
  apply Set.ext
  intro c
  obtain ⟨a,rfl⟩ := (T.atom p).surjective c
  rw [T.networkIso_apply]
  rw [(T.atom p).injective.mem_set_image]
  constructor
  · intro ha
    refine ⟨?_, ?_⟩
    · rw [T.networkIso_apply]
      exact Set.mem_image_of_mem _ ha.1
    · intro y hxy hyz
      obtain ⟨y,rfl⟩ := σ.surjective y
      have hx : p.src ≠ y := fun h => hxy (congrArg σ h)
      have hy : y ≠ p.dst := fun h => hyz (congrArg σ h)
      change T.atom p a ∈ S.product
        (T.networkIso N (pairEquiv σ ⟨p.src,y,hx⟩))
        (T.networkIso N (pairEquiv σ ⟨y,p.dst,hy⟩))
      rw [T.networkIso_apply, T.networkIso_apply]
      exact (T.product_iff p.src y p.dst hx hy p.ne _ _ a).mpr (ha.2 y hx hy)
  · intro ha
    refine ⟨?_, ?_⟩
    · have hb := ha.1
      rw [T.networkIso_apply] at hb
      exact (T.atom p).injective.mem_set_image.mp hb
    · intro y hx hy
      have hb := ha.2 (σ y) (fun h => hx (σ.injective h)) (fun h => hy (σ.injective h))
      change T.atom p a ∈ S.product
        (T.networkIso N (pairEquiv σ ⟨p.src,y,hx⟩))
        (T.networkIso N (pairEquiv σ ⟨y,p.dst,hy⟩)) at hb
      rw [T.networkIso_apply, T.networkIso_apply] at hb
      exact (T.product_iff p.src y p.dst hx hy p.ne _ _ a).mp hb

theorem stable_iff (N : Network D) :
    Stable E (T.networkIso N) ↔ Stable D N := by
  have hD : Stable D N ↔ step D N = N := ⟨fun h => funext h, fun h p => congrFun h p⟩
  have hE : Stable E (T.networkIso N) ↔ step E (T.networkIso N) = T.networkIso N :=
    ⟨fun h => funext h, fun h p => congrFun h p⟩
  rw [hD, hE, ← T.step_natural]
  exact T.networkIso.injective.eq_iff

/-- Greatestness transports the limit without comparing chosen indices. -/
theorem fixedNetwork_natural (hInitial : T.networkIso (initial D) = initial E) :
    T.networkIso (fixedNetwork D) = fixedNetwork E := by
  apply le_antisymm
  · apply fixedNetwork_greatest E _ ((T.stable_iff _).mpr (fixedNetwork_stable D))
    change T.networkIso (fixedNetwork D) ≤ initial E
    rw [← hInitial]
    exact T.networkIso.monotone (fixedNetwork_refines_initial D)
  · let M := T.networkIso.symm (fixedNetwork E)
    have hm : T.networkIso M = fixedNetwork E := T.networkIso.apply_symm_apply _
    have hStable : Stable D M := (T.stable_iff M).mp (hm.symm ▸ fixedNetwork_stable E)
    have hInside : M ≤ initial D := by
      apply T.networkIso.le_iff_le.mp
      rw [hm, hInitial]
      exact fixedNetwork_refines_initial E
    have hGreatest := T.networkIso.monotone (fixedNetwork_greatest D M hStable hInside)
    rw [hm] at hGreatest
    exact hGreatest

/-- Initial covariance reduces to the actual record/hole equation. In
particular an absent edge, including equal-index distinct clones, stays Top. -/
theorem initial_natural_of_edges
    (hEdges : ∀ p : DistinctPair V,
      E.edge (σ p.src) (σ p.dst) (fun h => p.ne (σ.injective h)) =
        (D.edge p.src p.dst p.ne).map (T.atom p)) :
    T.networkIso (initial D) = initial E := by
  funext q
  obtain ⟨p,rfl⟩ := (pairEquiv σ).surjective q
  rw [T.networkIso_apply]
  simp only [initial, pairEquiv, Equiv.coe_fn_mk]
  rw [hEdges p]
  cases D.edge p.src p.dst p.ne with
  | none => exact Set.image_univ.trans (T.atom p).surjective.range_eq
  | some a => exact Set.image_singleton

theorem converse_natural (N : Network D) (hN : ConverseClosed D N) :
    ConverseClosed E (T.networkIso N) := by
  intro q
  obtain ⟨p,rfl⟩ := (pairEquiv σ).surjective q
  change T.networkIso N (pairEquiv σ ⟨p.dst,p.src,p.ne.symm⟩) =
    S.opposite (T.networkIso N (pairEquiv σ p))
  rw [T.networkIso_apply, T.networkIso_apply, hN p]
  ext b
  obtain ⟨a,rfl⟩ := (T.atom ⟨p.dst,p.src,p.ne.symm⟩).surjective b
  rw [(T.atom _).injective.mem_set_image]
  change S.conv a ∈ N p ↔ S.conv (T.atom ⟨p.dst,p.src,p.ne.symm⟩ a) ∈ T.atom p '' N p
  rw [← T.converse ⟨p.dst,p.src,p.ne.symm⟩ a]
  exact ((T.atom p).injective.mem_set_image).symm

end PCTransport

/-- Equality transport changes only endpoint indices, never the atom. -/
def castAtomEquiv {i j i' j' : ι} (hi : i = i') (hj : j = j') :
    S.Atom i j ≃ S.Atom i' j' := by
  cases hi
  cases hj
  exact Equiv.refl _

theorem castAtom_triangle {i j k i' j' k' : ι}
    (hi : i = i') (hj : j = j') (hk : k = k')
    (a : S.Atom i j) (b : S.Atom j k) (c : S.Atom i k) :
    S.Triangle (castAtomEquiv hi hj a) (castAtomEquiv hj hk b) (castAtomEquiv hi hk c) ↔
      S.Triangle a b c := by cases hi; cases hj; cases hk; rfl

theorem castAtom_converse {i j i' j' : ι} (hi : i = i') (hj : j = j')
    (a : S.Atom i j) :
    castAtomEquiv hj hi (S.conv a) = S.conv (castAtomEquiv hi hj a) := by
  cases hi; cases hj; rfl

section Gauge
variable {Γ : Type t} [Group Γ] {N : Type r} {A : Selectors.PureTagAction S Γ N}
variable {K : Type s} [CommGroup K] (Q : EndpointGauge S A K)

/-- The two independently chosen endpoint switches commute on atoms,
by literal-name injectivity, even when their owner types coincide. -/
theorem gauge_left_right (g h : K) {i j : ι} (a : S.Atom i j) :
    Q.left g (Q.right h a) = Q.right h (Q.left g a) := by
  apply A.label_injective
  rw [Q.left_label,Q.right_label,Q.right_label,Q.left_label]
  have he : Q.switch g * Q.switch h = Q.switch h * Q.switch g := by
    rw [← Q.switch.map_mul, ← Q.switch.map_mul, mul_comm g h]
  exact congrArg (fun e : Equiv.Perm N => e (A.label a)) he

noncomputable def gaugeAtom (g h : K) (i j : ι) :
    S.Atom i j ≃ S.Atom (Q.owner g i) (Q.owner h j) :=
  (Q.right h).trans (Q.left g)

theorem gauge_triangle (hConv : LiteralConverse S A) (g h k : K) {i j m : ι}
    (a : S.Atom i j) (b : S.Atom j m) (c : S.Atom i m) :
    S.Triangle a b c ↔ S.Triangle
      (gaugeAtom Q g h i j a) (gaugeAtom Q h k j m b) (gaugeAtom Q g k i m c) := by
  change S.Triangle a b c ↔ S.Triangle
    (Q.left g (Q.right h a)) (Q.left h (Q.right k b)) (Q.left g (Q.right k c))
  rw [gauge_left_right Q h k b, gauge_left_right Q g k c]
  exact triangle_independent_switch Q hConv g h k a b c

theorem gauge_converse (hConv : LiteralConverse S A) (g h : K) {i j : ι}
    (a : S.Atom i j) :
    gaugeAtom Q h g j i (S.conv a) = S.conv (gaugeAtom Q g h i j a) := by
  change Q.left h (Q.right g (S.conv a)) = S.conv (Q.left g (Q.right h a))
  rw [right_conv Q hConv, left_conv Q hConv, ← gauge_left_right Q g h a]

def gaugeMenu (g h : K) {i j : ι} (D : S.Menu i j) :
    S.Menu (Q.owner g i) (Q.owner h j) := gaugeAtom Q g h i j '' D

/-- The middle switch cancels for arbitrary Boolean menus, including
empty and nonexact ones, with all three endpoint gauges independent. -/
theorem gauge_product (hConv : LiteralConverse S A) (g h k : K) {i j m : ι}
    (D : S.Menu i j) (F : S.Menu j m) :
    S.product (gaugeMenu Q g h D) (gaugeMenu Q h k F) =
      gaugeMenu Q g k (S.product D F) := by
  ext c
  obtain ⟨c,rfl⟩ := (gaugeAtom Q g k i m).surjective c
  simp only [gaugeMenu]
  rw [(gaugeAtom Q g k i m).injective.mem_set_image]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,ht⟩
    exact ⟨a,ha,b,hb,(gauge_triangle Q hConv g h k a b c).mpr ht⟩
  · rintro ⟨a,ha,b,hb,ht⟩
    exact ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,(gauge_triangle Q hConv g h k a b c).mp ht⟩

theorem gauge_inter (g h : K) {i j : ι} (D F : S.Menu i j) :
    gaugeMenu Q g h (D ∩ F) = gaugeMenu Q g h D ∩ gaugeMenu Q g h F :=
  Set.image_inter (gaugeAtom Q g h i j).injective

theorem gauge_opposite (hConv : LiteralConverse S A) (g h : K) {i j : ι}
    (D : S.Menu i j) : gaugeMenu Q h g (S.opposite D) = S.opposite (gaugeMenu Q g h D) := by
  ext c
  obtain ⟨a,rfl⟩ := (gaugeAtom Q h g j i).surjective c
  simp only [gaugeMenu]
  rw [(gaugeAtom Q h g j i).injective.mem_set_image]
  change S.conv a ∈ D ↔ S.conv (gaugeAtom Q h g j i a) ∈ gaugeAtom Q g h i j '' D
  rw [← gauge_converse Q hConv h g a]
  exact ((gaugeAtom Q g h i j).injective.mem_set_image).symm

/-- This constructor accepts B026's proved actual endpoint gauge directly;
it asks for no safe-system or completion-equivariance premise. -/
noncomputable def gaugeTransport (hConv : LiteralConverse S A) (δ : V → K)
    (hSort : ∀ x, E.vertexSort (σ x) = Q.owner (δ x) (D.vertexSort x)) :
    PCTransport D E σ where
  atom p := (gaugeAtom Q (δ p.src) (δ p.dst) _ _).trans
    (castAtomEquiv (hSort p.src).symm (hSort p.dst).symm)
  triangle := by
    intro x y z hxy hyz hxz a b c
    change S.Triangle a b c ↔ S.Triangle
      (castAtomEquiv (hSort x).symm (hSort y).symm (gaugeAtom Q (δ x) (δ y) _ _ a))
      (castAtomEquiv (hSort y).symm (hSort z).symm (gaugeAtom Q (δ y) (δ z) _ _ b))
      (castAtomEquiv (hSort x).symm (hSort z).symm (gaugeAtom Q (δ x) (δ z) _ _ c))
    rw [castAtom_triangle]
    exact gauge_triangle Q hConv (δ x) (δ y) (δ z) a b c
  converse := by
    intro p a
    change castAtomEquiv (hSort p.dst).symm (hSort p.src).symm
      (gaugeAtom Q (δ p.dst) (δ p.src) _ _ (S.conv a)) = _
    rw [gauge_converse Q hConv, castAtom_converse]
    rfl

end Gauge

section Pure
variable {Γ : Type t} [Group Γ] {N : Type r} (P : PaletteRelabelling S Γ N)

theorem pure_triangle (γ : Γ) {i j k : ι}
    (a : S.Atom i j) (b : S.Atom j k) (c : S.Atom i k) :
    S.Triangle a b c ↔ S.Triangle
      (P.atomEquiv γ i j a) (P.atomEquiv γ j k b) (P.atomEquiv γ i k c) :=
  P.triangle γ a b c _ _ _ (P.atomMove_label γ a) (P.atomMove_label γ b) (P.atomMove_label γ c)

theorem pure_converse (γ : Γ) {i j : ι} (a : S.Atom i j) :
    P.atomEquiv γ j i (S.conv a) = S.conv (P.atomEquiv γ i j a) := by
  apply P.label_injective
  change P.label (P.atomMove γ (S.conv a)) = P.label (S.conv (P.atomMove γ a))
  rw [P.atomMove_label,P.converse_label,P.converse_label,P.atomMove_label]

/-- Pure owner transport preserves literal original fine names. -/
noncomputable def pureTransport (γ : Γ)
    (hSort : ∀ x, E.vertexSort (σ x) = P.owner γ (D.vertexSort x)) :
    PCTransport D E σ where
  atom p := (P.atomEquiv γ _ _).trans
    (castAtomEquiv (hSort p.src).symm (hSort p.dst).symm)
  triangle := by
    intro x y z hxy hyz hxz a b c
    change S.Triangle a b c ↔ S.Triangle
      (castAtomEquiv (hSort x).symm (hSort y).symm (P.atomEquiv γ _ _ a))
      (castAtomEquiv (hSort y).symm (hSort z).symm (P.atomEquiv γ _ _ b))
      (castAtomEquiv (hSort x).symm (hSort z).symm (P.atomEquiv γ _ _ c))
    rw [castAtom_triangle]
    exact pure_triangle P γ a b c
  converse := by
    intro p a
    change castAtomEquiv (hSort p.dst).symm (hSort p.src).symm
      (P.atomEquiv γ _ _ (S.conv a)) = _
    rw [pure_converse P, castAtom_converse]
    rfl

/-- The displayed transported atom has exactly its original raw name. -/
theorem pureTransport_label (γ : Γ)
    (hSort : ∀ x, E.vertexSort (σ x) = P.owner γ (D.vertexSort x))
    (p : DistinctPair V) (a : S.Atom (D.vertexSort p.src) (D.vertexSort p.dst)) :
    P.label ((pureTransport D E σ P γ hSort).atom p a) = P.label a := by
  change P.label (castAtomEquiv (hSort p.src).symm (hSort p.dst).symm
    (P.atomEquiv γ _ _ a)) = P.label a
  have hCast : ∀ {i j i' j' : ι} (hi : i = i') (hj : j = j') (b : S.Atom i j),
      P.label (castAtomEquiv hi hj b) = P.label b := by
    intro i j i' j' hi hj b
    cases hi; cases hj; rfl
  rw [hCast]
  exact P.atomMove_label γ a
end Pure

section Combined
variable {Γ : Type t} [Group Γ] {N : Type r} (P : PaletteRelabelling S Γ N)
variable {K : Type s} [CommGroup K] (Q : EndpointGauge S P.pureAction K)

/-- The pure owner permutation is followed by separately chosen endpoint
switches. Their effects on raw names are kept explicit. -/
noncomputable def pureGaugeTransport (γ : Γ) (δ : V → K)
    (hSort : ∀ x, E.vertexSort (σ x) = Q.owner (δ x) (P.owner γ (D.vertexSort x))) :
    PCTransport D E σ where
  atom p := ((P.atomEquiv γ _ _).trans (gaugeAtom Q (δ p.src) (δ p.dst) _ _)).trans
    (castAtomEquiv (hSort p.src).symm (hSort p.dst).symm)
  triangle := by
    intro x y z hxy hyz hxz a b c
    change S.Triangle a b c ↔ S.Triangle
      (castAtomEquiv (hSort x).symm (hSort y).symm
        (gaugeAtom Q (δ x) (δ y) _ _ (P.atomEquiv γ _ _ a)))
      (castAtomEquiv (hSort y).symm (hSort z).symm
        (gaugeAtom Q (δ y) (δ z) _ _ (P.atomEquiv γ _ _ b)))
      (castAtomEquiv (hSort x).symm (hSort z).symm
        (gaugeAtom Q (δ x) (δ z) _ _ (P.atomEquiv γ _ _ c)))
    rw [castAtom_triangle]
    exact (pure_triangle P γ a b c).trans
      (gauge_triangle Q P.literalConverse (δ x) (δ y) (δ z) _ _ _)
  converse := by
    intro p a
    change castAtomEquiv (hSort p.dst).symm (hSort p.src).symm
      (gaugeAtom Q (δ p.dst) (δ p.src) _ _ (P.atomEquiv γ _ _ (S.conv a))) = _
    rw [pure_converse P, gauge_converse Q P.literalConverse, castAtom_converse]
    rfl

theorem pureGaugeTransport_label (γ : Γ) (δ : V → K)
    (hSort : ∀ x, E.vertexSort (σ x) = Q.owner (δ x) (P.owner γ (D.vertexSort x)))
    (p : DistinctPair V) (a : S.Atom (D.vertexSort p.src) (D.vertexSort p.dst)) :
    P.label ((pureGaugeTransport D E σ P Q γ δ hSort).atom p a) =
      Q.switch (δ p.src) (Q.switch (δ p.dst) (P.label a)) := by
  change P.label (castAtomEquiv (hSort p.src).symm (hSort p.dst).symm
    (Q.left (δ p.src) (Q.right (δ p.dst) (P.atomEquiv γ _ _ a)))) = _
  have hCast : ∀ {i j i' j' : ι} (hi : i = i') (hj : j = j') (b : S.Atom i j),
      P.label (castAtomEquiv hi hj b) = P.label b := by
    intro i j i' j' hi hj b
    cases hi; cases hj; rfl
  rw [hCast]
  change P.pureAction.label (Q.left (δ p.src) (Q.right (δ p.dst) (P.atomEquiv γ _ _ a))) = _
  rw [Q.left_label,Q.right_label]
  change Q.switch (δ p.src) (Q.switch (δ p.dst) (P.label (P.atomMove γ a))) = _
  rw [P.atomMove_label]
end Combined

namespace Actual
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge TransversalSource
variable {M : Type v} (S₀ : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S₀ G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S₀ H)
variable (B : Finset (Owner S₀ H R)) (hB : PacketInvariant S₀ H R B)
variable (Δ : Subgroup (TransversalPure.Gamma S₀ H R B))
variable (hΔ : ∀ g, TransversalPure.diagonal S₀ H R B hB g ∈ Δ)

/-- Actual residual-source instance: all endpoint and pure-action laws
come from accepted B026, not from new caller-supplied providers. -/
noncomputable def pureGaugeTransport
    (D : PartialDiagram (source S₀ H R B) V) (E : PartialDiagram (source S₀ H R B) W)
    (σ : V ≃ W) (γ : Δ) (δ : V → ResidualData.PacketGroup S₀ H)
    (hSort : ∀ x, E.vertexSort (σ x) =
      TransversalGauge.ownerHom S₀ H R B hB (δ x)
        ((TransversalPure.subgroupRelabelling S₀ H R B hB Δ).owner γ (D.vertexSort x))) :
    PCTransport D E σ := by
  letI := TransversalPure.thinCommGroup S₀ H R
  exact FullRows.pureGaugeTransport D E σ
    (TransversalPure.subgroupRelabelling S₀ H R B hB Δ)
    (TransversalPure.subgroupEndpointGauge S₀ H R B hB Δ hΔ) γ δ hSort
end Actual

end CCO.FullRows
