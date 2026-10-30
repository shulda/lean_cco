import CCO.ResetOrder.Hierarchy.Synchronize

/-! Strict coarsening remains well founded after identifying transition
orbits, because actual upper-interval rank is constant on each orbit. -/
universe u v w
namespace CCO.ResetOrder.Hierarchy
namespace Schedule
variable {I : Type u} (H : Schedule I)
def Coarser (i j : I) : Prop := ∃ a, H.coordinate j a = i
theorem coarser_wellFounded : WellFounded H.Coarser :=
  (measure H.rank).wf.mono (fun _ _ h => by obtain ⟨a,rfl⟩ := h; exact H.coordinate_rank _ a)
end Schedule

namespace Charting
variable {R : Type u} {J : R → Type u} {H : Schedule (Sigma J)}
variable {X : Sigma J → Type v} {S : System H X} {rep : ∀ r, J r} (C : Charting.{u,v,w} S rep)

def CoarserOrbit (_C : Charting.{u,v,w} S rep) (r s : R) : Prop :=
  ∃ i : Sigma J, ∃ a : Fin (H.count i), i.1 = s ∧ (H.coordinate i a).1 = r

theorem coarserOrbit_rank {r s : R} (h : C.CoarserOrbit r s) :
    H.rank ⟨r,rep r⟩ < H.rank ⟨s,rep s⟩ := by
  obtain ⟨⟨s',i⟩,a,hi,hr⟩ := h
  change s' = s at hi
  subst s'
  have hc := H.coordinate_rank ⟨s,i⟩ a
  have hs := C.rank_orbit s i
  have hk := C.rank_orbit (H.coordinate ⟨s,i⟩ a).1 (H.coordinate ⟨s,i⟩ a).2
  rw [hs, hk] at hc
  exact hr ▸ hc

theorem coarserOrbit_wellFounded : WellFounded C.CoarserOrbit :=
  (measure (fun r => H.rank ⟨r,rep r⟩)).wf.mono (fun _ _ h => C.coarserOrbit_rank h)

theorem no_orbit_self_coarsening (r : R) : ¬ C.CoarserOrbit r r :=
  fun h => Nat.lt_irrefl _ (C.coarserOrbit_rank h)
end Charting
end CCO.ResetOrder.Hierarchy
