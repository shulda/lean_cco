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
end CCO.FullRows
