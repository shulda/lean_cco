import CCO.RankInduction.Basis
import CCO.AclOwners.Avoidance
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-! One finite-coset avoidance motion strongly amalgamates every finite
absolutely closed span for the full diversity palette. The resulting
finite union is not claimed closed. No CCO or EPPA enters this proof. -/

universe v w t
namespace CCO.RankInduction
open FiniteLift

variable {M : Type v} {G : Type t} [Group G] [MulAction G M]

/-- Actual pointwise stabilizer orbits, with the exact real base. -/
theorem fixing_orbit_eq (C : Set M) (x : M) :
    MulAction.orbit (fixingSubgroup G C) x = orbitSet G C x := by
  ext y
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.val, (mem_fixingSubgroup_iff G).mp g.property, hg⟩
  · rintro ⟨g, hC, hg⟩
    exact ⟨⟨g, (mem_fixingSubgroup_iff G).mpr hC⟩, hg⟩

/-- One base-fixing element simultaneously avoids all requested finite
off-base points and all forbidden points. Empty requests are allowed. -/
theorem avoid_over_closed_base (C A Z : Set M)
    (closed : aclSet G C = C) (finiteA : A.Finite) (finiteZ : Z.Finite)
    (off : ∀ x ∈ A, x ∉ C) :
    ∃ g : G, (∀ c ∈ C, g • c = c) ∧ Disjoint ((g • ·) '' A) Z := by
  classical
  have infinite (x : M) (hx : x ∈ finiteA.toFinset) :
      (MulAction.orbit (fixingSubgroup G C) x).Infinite := by
    rw [fixing_orbit_eq]
    intro hf
    have hc : x ∈ aclSet G C := hf
    rw [closed] at hc
    exact off x (by simpa only [Set.Finite.mem_toFinset] using hx) hc
  obtain ⟨g, hg⟩ := AclOwners.finite_action_avoidance_disjoint
    (G := fixingSubgroup G C) finiteA.toFinset finiteZ.toFinset infinite
  refine ⟨g.val, (mem_fixingSubgroup_iff G).mp g.property, ?_⟩
  simpa only [Set.Finite.coe_toFinset, MulAction.subgroup_smul_def] using hg

variable (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (H : HomogeneousSource S G)

include H in
/-- C07--C08. Both arbitrary finite base maps are aligned on their WHOLE
domain. A single stabilizer motion separates all off-base intersections.
Only the base's absolute closure is needed; the output need not be closed. -/
theorem full_palette_strong_closed_amalgamation :
    StrongClosedAmalgamation G (aclSet G) (S.menuRel (i := ()) (j := ()) Set.univ) := by
  classical
  intro C L R finiteC finiteL finiteR closedC _closedL _closedR f g
  obtain ⟨lf, hlf⟩ := real_embedding_lift S H finiteC f
  obtain ⟨rg, hrg⟩ := real_embedding_lift S H finiteC g
  let L' : Set M := (lf⁻¹ • ·) '' L
  let R' : Set M := (rg⁻¹ • ·) '' R
  have finiteL' : L'.Finite := finiteL.image _
  have finiteR' : R'.Finite := finiteR.image _
  obtain ⟨k, hk, disjoint⟩ := avoid_over_closed_base C (R' \ C) L'
    closedC finiteR'.sdiff finiteL' (fun _ h => h.2)
  have baseL (c : C) : lf⁻¹ • (f.toEmbedding c).val = c.val := by
    rw [← hlf c, inv_smul_smul]
  have baseR (c : C) : rg⁻¹ • (g.toEmbedding c).val = c.val := by
    rw [← hrg c, inv_smul_smul]
  have oldR (y : R) : rg⁻¹ • y.val ∈ R' := ⟨y.val, y.property, rfl⟩
  have oldL (x : L) : lf⁻¹ • x.val ∈ L' := ⟨x.val, x.property, rfl⟩
  have offR (y : R) (hy : y ∉ Set.range g.toEmbedding) : rg⁻¹ • y.val ∈ R' \ C := by
    refine ⟨oldR y, ?_⟩
    intro hc
    let c : C := ⟨rg⁻¹ • y.val, hc⟩
    apply hy
    refine ⟨c, Subtype.ext ?_⟩
    rw [← hrg c]
    exact smul_inv_smul rg y.val
  let W : Set M := L' ∪ (k • ·) '' R'
  have finiteW : W.Finite := finiteL'.union (finiteR'.image _)
  let l : OrbitalEmbedding G L W := {
    toEmbedding := {
      toFun := fun x => ⟨lf⁻¹ • x.val, Or.inl (oldL x)⟩
      inj' := fun _ _ he => Subtype.ext ((MulAction.injective lf⁻¹) (congrArg Subtype.val he)) }
    pair := fun x y => ⟨lf⁻¹, rfl, rfl⟩ }
  let r : OrbitalEmbedding G R W := {
    toEmbedding := {
      toFun := fun y => ⟨k • (rg⁻¹ • y.val), Or.inr ⟨rg⁻¹ • y.val, oldR y, rfl⟩⟩
      inj' := fun _ _ he => Subtype.ext ((MulAction.injective rg⁻¹)
        ((MulAction.injective k) (congrArg Subtype.val he))) }
    pair := fun x y => ⟨k * rg⁻¹, mul_smul _ _ _, mul_smul _ _ _⟩ }
  have commute (c : C) : l.toEmbedding (f.toEmbedding c) = r.toEmbedding (g.toEmbedding c) := by
    apply Subtype.ext
    change lf⁻¹ • (f.toEmbedding c).val = k • (rg⁻¹ • (g.toEmbedding c).val)
    rw [baseL c, baseR c, hk c.val c.property]
  have strong (x : L) (y : R) : l.toEmbedding x = r.toEmbedding y ↔
      ∃ c, f.toEmbedding c = x ∧ g.toEmbedding c = y := by
    constructor
    · intro he
      by_cases hy : y ∈ Set.range g.toEmbedding
      · obtain ⟨c, hcy⟩ := hy
        refine ⟨c, l.toEmbedding.injective ?_, hcy⟩
        exact (commute c).trans ((congrArg r.toEmbedding hcy).trans he.symm)
      · have hv : k • (rg⁻¹ • y.val) = lf⁻¹ • x.val := (congrArg Subtype.val he).symm
        exact False.elim (Set.disjoint_left.mp disjoint
          ⟨rg⁻¹ • y.val, offR y hy, hv⟩ (oldL x))
    · rintro ⟨c, rfl, rfl⟩
      exact commute c
  refine ⟨W, finiteW, l, r, commute, strong, ?_⟩
  intro x y hx _hy
  have ne : (l.toEmbedding x).val ≠ (r.toEmbedding y).val := by
    intro he
    obtain ⟨c, hc, _⟩ := (strong x y).mp (Subtype.ext he)
    exact hx ⟨c, hc⟩
  cases hc : S.colour (i := ()) (j := ()) (l.toEmbedding x).val (r.toEmbedding y).val with
  | none =>
    exact False.elim (ne (eq_of_heq (Sigma.mk.inj ((S.colour_none_iff _ _).mp hc)).2))
  | some a => exact ⟨a, Set.mem_univ _, hc⟩

end CCO.RankInduction
