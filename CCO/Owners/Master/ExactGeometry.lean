import CCO.Owners.Master.ExactCoordinates
import CCO.Owners.Master.UpsetSchedule
import CCO.Owners.Master.Diagram

/-! The fixed ambient diagram and its genuine fine-coloured binary
pullbacks. Every component is a literal quotient of the original source. -/

universe v w t
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)

@[reducible] def exactAmbient : Diagram.Ambient (Position S H cco) where
  X := Coordinate S H cco
  r := coordinateMap S H cco
  r_id := coordinateMap_id S H cco
  r_comp := coordinateMap_comp S H cco

section Kernels
variable (K E F O : Exact S H cco)
local instance invariantK : CanonicalQuotients.Invariant G K.val := Product.exactInvariant S H cco K
local instance invariantE : CanonicalQuotients.Invariant G E.val := Product.exactInvariant S H cco E
local instance invariantF : CanonicalQuotients.Invariant G F.val := Product.exactInvariant S H cco F
local instance invariantO : CanonicalQuotients.Invariant G O.val := Product.exactInvariant S H cco O

def kernelGeometry (hK : K = E ⊓ F) (hO : O = E ⊔ F) :
    Product.ProductGeometry (G := G) (K := Quotient K.val)
      (ED := Quotient E.val) (JC := Quotient F.val) (O := Quotient O.val) := by
  cases hK
  cases hO
  exact Product.sourceGeometry S H cco E F

theorem kernelGeometry_pD (hK : K = E ⊓ F) (hO : O = E ⊔ F)
    (hKE : K ≤ E) (x : Quotient K.val) :
    (kernelGeometry S H cco K E F O hK hO).pD x = Abstract.quotientMap hKE x := by
  induction x using Quotient.inductionOn with
  | _ a => cases hK; cases hO; rfl

theorem kernelGeometry_pC (hK : K = E ⊓ F) (hO : O = E ⊔ F)
    (hKF : K ≤ F) (x : Quotient K.val) :
    (kernelGeometry S H cco K E F O hK hO).pC x = Abstract.quotientMap hKF x := by
  induction x using Quotient.inductionOn with
  | _ a => cases hK; cases hO; rfl

theorem kernelGeometry_rD (hK : K = E ⊓ F) (hO : O = E ⊔ F)
    (hEO : E ≤ O) (x : Quotient E.val) :
    (kernelGeometry S H cco K E F O hK hO).rD x = Abstract.quotientMap hEO x := by
  induction x using Quotient.inductionOn with
  | _ a => cases hK; cases hO; rfl

theorem kernelGeometry_rC (hK : K = E ⊓ F) (hO : O = E ⊔ F)
    (hFO : F ≤ O) (x : Quotient F.val) :
    (kernelGeometry S H cco K E F O hK hO).rC x = Abstract.quotientMap hFO x := by
  induction x using Quotient.inductionOn with
  | _ a => cases hK; cases hO; rfl
end Kernels

variable {U V : Finset (Position S H cco)} {p : Position S H cco}

theorem new_kernel_inf (upU : IsUpset U) (next : Next U p)
    (upV : IsUpset V) (within : V ⊆ insert p U) (hp : p ∈ V) :
    coordinateKernel S H cco V = coordinateKernel S H cco (V.erase p) ⊓
      coordinateKernel S H cco (insert p (strictUpper p)) := by
  rw [strictUpper_insert]
  rw [← coordinateKernel_union S H cco _ _ (next_erase_upset upU next upV within)
    (principalUpper_upset p),next_erase_union_principal upV hp]

theorem new_kernel_sup (upU : IsUpset U) (next : Next U p)
    (upV : IsUpset V) (within : V ⊆ insert p U) (hp : p ∈ V) :
    coordinateKernel S H cco (strictUpper p) = coordinateKernel S H cco (V.erase p) ⊔
      coordinateKernel S H cco (insert p (strictUpper p)) := by
  rw [strictUpper_insert]
  rw [← coordinateKernel_inter S H cco _ _ (next_erase_upset upU next upV within)
    (principalUpper_upset p),next_erase_inter_principal upV hp]

def stepGeometry (upU : IsUpset U) (next : Next U p)
    (upV : IsUpset V) (within : V ⊆ insert p U) (hp : p ∈ V) :
    Product.ProductGeometry (G := G) (K := Coordinate S H cco V)
      (ED := Coordinate S H cco (V.erase p))
      (JC := Coordinate S H cco (insert p (strictUpper p)))
      (O := Coordinate S H cco (strictUpper p)) :=
  kernelGeometry S H cco _ _ _ _ (new_kernel_inf S H cco upU next upV within hp)
    (new_kernel_sup S H cco upU next upV within hp)

@[simp] theorem stepGeometry_pD (upU : IsUpset U) (next : Next U p)
    (upV : IsUpset V) (within : V ⊆ insert p U) (hp : p ∈ V)
    (x : Coordinate S H cco V) :
    (stepGeometry S H cco upU next upV within hp).pD x =
      coordinateMap S H cco (Finset.erase_subset p V) x :=
  kernelGeometry_pD S H cco _ _ _ _ _ _ _ x

@[simp] theorem stepGeometry_pC (upU : IsUpset U) (next : Next U p)
    (upV : IsUpset V) (within : V ⊆ insert p U) (hp : p ∈ V)
    (x : Coordinate S H cco V) :
    (stepGeometry S H cco upU next upV within hp).pC x =
      coordinateMap S H cco (Finset.insert_subset hp
        ((next_strictUpper_subset_erase upV hp).trans (Finset.erase_subset p V))) x :=
  kernelGeometry_pC S H cco _ _ _ _ _ _ _ x

@[simp] theorem stepGeometry_rD (upU : IsUpset U) (next : Next U p)
    (upV : IsUpset V) (within : V ⊆ insert p U) (hp : p ∈ V)
    (x : Coordinate S H cco (V.erase p)) :
    (stepGeometry S H cco upU next upV within hp).rD x =
      coordinateMap S H cco (next_strictUpper_subset_erase upV hp) x :=
  kernelGeometry_rD S H cco _ _ _ _ _ _ _ x

@[simp] theorem stepGeometry_rC (upU : IsUpset U) (next : Next U p)
    (upV : IsUpset V) (within : V ⊆ insert p U) (hp : p ∈ V)
    (x : Coordinate S H cco (insert p (strictUpper p))) :
    (stepGeometry S H cco upU next upV within hp).rC x =
      coordinateMap S H cco (Finset.subset_insert p (strictUpper p)) x :=
  kernelGeometry_rC S H cco _ _ _ _ _ _ _ x

/-- The binary ambient square is the FULL actual pullback. This supplies
the only geometric gluing input of the independent finite diagram step. -/
theorem step_glue (upU : IsUpset U) (next : Next U p)
    (upV : IsUpset V) (within : V ⊆ insert p U) (hp : p ∈ V)
    (b : Coordinate S H cco (V.erase p))
    (x : Coordinate S H cco (insert p (strictUpper p)))
    (owner : coordinateMap S H cco (next_strictUpper_subset_erase upV hp) b =
      coordinateMap S H cco (Finset.subset_insert p (strictUpper p)) x) :
    ∃! y : Coordinate S H cco V,
      coordinateMap S H cco (Finset.erase_subset p V) y = b ∧
        coordinateMap S H cco (Finset.insert_subset hp
          ((next_strictUpper_subset_erase upV hp).trans (Finset.erase_subset p V))) y = x := by
  let P := stepGeometry S H cco upU next upV within hp
  let pair : Product.Pullback P.rD P.rC := ⟨(b,x),by
    simpa only [P,stepGeometry_rD,stepGeometry_rC] using owner⟩
  let y := P.full.symm pair
  have hyD : P.pD y = b := by
    simpa only [y,Equiv.apply_symm_apply,pair] using (P.full_fst y).symm
  have hyC : P.pC y = x := by
    simpa only [y,Equiv.apply_symm_apply,pair] using (P.full_snd y).symm
  refine ⟨y,?_,?_⟩
  · exact ⟨(stepGeometry_pD S H cco upU next upV within hp y).symm.trans hyD,
      (stepGeometry_pC S H cco upU next upV within hp y).symm.trans hyC⟩
  · intro z hz
    apply P.full.injective
    apply Subtype.ext
    apply Prod.ext
    · calc
        _ = P.pD z := P.full_fst z
        _ = b := (stepGeometry_pD S H cco upU next upV within hp z).trans hz.1
        _ = _ := hyD.symm.trans (P.full_fst y).symm
    · calc
        _ = P.pC z := P.full_snd z
        _ = x := (stepGeometry_pC S H cco upU next upV within hp z).trans hz.2
        _ = _ := hyC.symm.trans (P.full_snd y).symm

end
end CCO.Owners.Master
