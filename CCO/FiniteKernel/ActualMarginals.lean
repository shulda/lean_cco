import CCO.FiniteKernel.Patching

/-! Actual binding images and actual pair images. Subdirectness concerns the
ACTUAL images, never arbitrary intrinsic groups or hidden finite projections. -/

universe u v w z
namespace CCO.FiniteKernel.FinitePartition
noncomputable section
variable {X : Type u} {S : BinaryStructure.{u,v,w} X} {I : Type z}
variable (P : FinitePartition S I)

def binding (i : I) : Subgroup (P.Intrinsic i) := (P.restrictFibre i).range

def pairRestriction (i j : I) : P.kernel →* (P.Intrinsic i × P.Intrinsic j) where
  toFun g := (P.restrictFibre i g,P.restrictFibre j g)
  map_one' := by simp only [map_one,Prod.one_eq_mk]
  map_mul' g h := by simp only [map_mul,Prod.mk_mul_mk]

def actualPair (i j : I) : Subgroup (P.Intrinsic i × P.Intrinsic j) :=
  (P.pairRestriction i j).range

def bindingRestriction (i : I) : P.kernel →* P.binding i :=
  (P.restrictFibre i).rangeRestrict

def actualBindingPairMap (i j : I) : P.kernel →* (P.binding i × P.binding j) where
  toFun g := (P.bindingRestriction i g,P.bindingRestriction j g)
  map_one' := by simp only [map_one,Prod.one_eq_mk]
  map_mul' g h := by simp only [map_mul,Prod.mk_mul_mk]

def actualBindingPair (i j : I) : Subgroup (P.binding i × P.binding j) :=
  (P.actualBindingPairMap i j).range

theorem actual_pair_subdirect_left (i j : I) (g : P.binding i) :
    ∃ h : P.binding j, (g,h) ∈ P.actualBindingPair i j := by
  obtain ⟨n,hn⟩ := g.property
  refine ⟨P.bindingRestriction j n,n,?_⟩
  apply Prod.ext
  · exact Subtype.ext hn
  · rfl

theorem actual_pair_subdirect_right (i j : I) (h : P.binding j) :
    ∃ g : P.binding i, (g,h) ∈ P.actualBindingPair i j := by
  obtain ⟨n,hn⟩ := h.property
  refine ⟨P.bindingRestriction i n,n,?_⟩
  apply Prod.ext
  · rfl
  · exact Subtype.ext hn

theorem actual_pair_compatible {i j : I} (hij : i ≠ j)
    {g : P.Intrinsic i} {h : P.Intrinsic j} (hp : (g,h) ∈ P.actualPair i j) :
    P.Compatible g h := by
  obtain ⟨n,hn⟩ := hp
  have hi : P.restrictFibre i n = g := congrArg Prod.fst hn
  have hj : P.restrictFibre j n = h := congrArg Prod.snd hn
  exact hi ▸ hj ▸ P.rho_mem n i j hij

/-- C05 global reconstruction from all actual marginals. This theorem does
NOT identify any selected finite projection with its internal pair CSP. -/
theorem actual_marginal_reconstruction (p : ∀ i, P.Intrinsic i) :
    p ∈ Set.range P.rho ↔
      (∀ i, p i ∈ P.binding i) ∧
      ∀ i j, i ≠ j → (p i,p j) ∈ P.actualPair i j := by
  constructor
  · rintro ⟨n,rfl⟩
    exact ⟨fun i => ⟨n,rfl⟩,fun i j _ => ⟨n,rfl⟩⟩
  · rintro ⟨_,hp⟩
    exact (P.mem_range_rho p).mpr (fun i j hij => P.actual_pair_compatible hij (hp i j hij))

def projection (A : Finset I) : P.kernel →* (∀ i : ↥A, P.Intrinsic i.val) where
  toFun g i := P.restrictFibre i.val g
  map_one' := by funext i; exact (P.restrictFibre i.val).map_one
  map_mul' g h := by funext i; exact (P.restrictFibre i.val).map_mul g h

theorem projection_solution (A : Finset I) (g : P.kernel) :
    P.projection A g ∈ P.solutions A := fun i j hij => P.rho_mem g i.val j.val hij

end
end CCO.FiniteKernel.FinitePartition
