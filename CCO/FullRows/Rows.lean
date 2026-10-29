import CCO.FullRows.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators

/-! Bijective affine lifts and effective-row identities. No source, CCO,
countability, owner freeness or correction legality enters these facts. -/
universe u v w
namespace CCO.FullRows
variable {I : Type u} {K : Type v} [CommGroup K]

def rowEquiv (s : Structural I K) (C : Matrix I K) (i : I) : Row I K ≃ Row I K where
  toFun := rowImage s C i
  invFun := fun f j => f (s.sigma j) * (C i j * s.offset i)⁻¹
  left_inv := by
    intro f; funext j
    simp [rowImage, mul_assoc]
  right_inv := by
    intro f; funext j
    simp [rowImage, mul_assoc]

@[simp] theorem rowEquiv_apply (s : Structural I K) (C : Matrix I K) (i : I)
    (f : Row I K) : rowEquiv s C i f = rowImage s C i f := rfl

def packetEquiv (s : Structural I K) (C : Matrix I K) : Packet I K ≃ Packet I K where
  toFun := packetMap s C
  invFun := fun p => (s.sigma.symm p.1,(rowEquiv s C (s.sigma.symm p.1)).symm p.2)
  left_inv := by
    rintro ⟨i,f⟩
    simp [packetMap, ← rowEquiv_apply]
  right_inv := by
    rintro ⟨i,f⟩
    simp [packetMap, ← rowEquiv_apply]

@[simp] theorem packetEquiv_apply (s : Structural I K) (C : Matrix I K)
    (p : Packet I K) : packetEquiv s C p = packetMap s C p := rfl

def verticalEquiv (s : Structural I K) : Vertex I K ≃ Vertex I K where
  toFun := fun x => (x.1,x.2 * s.offset x.1.1)
  invFun := fun x => (x.1,x.2 * (s.offset x.1.1)⁻¹)
  left_inv := by rintro ⟨p,z⟩; simp
  right_inv := by rintro ⟨p,z⟩; simp

def liftEquiv (s : Structural I K) (C : Matrix I K) : Vertex I K ≃ Vertex I K :=
  (verticalEquiv s).trans ((packetEquiv s C).prodCongr (Equiv.refl K))

@[simp] theorem liftEquiv_apply (s : Structural I K) (C : Matrix I K)
    (x : Vertex I K) : liftEquiv s C x = lift s C x := rfl

theorem lift_bijective (s : Structural I K) (C : Matrix I K) :
    Function.Bijective (lift s C) := (liftEquiv s C).bijective

@[simp] theorem projection_lift (s : Structural I K) (C : Matrix I K)
    (x : Vertex I K) : projection (lift s C x) = baseMap s (projection x) := rfl

theorem lift_translate (s : Structural I K) (C : Matrix I K) (g : K)
    (x : Vertex I K) : lift s C (translate g x) = translate g (lift s C x) := by
  simp [lift,translate,mul_assoc]

theorem same_packet_lift_iff (s : Structural I K) (C : Matrix I K)
    (x y : Vertex I K) : (lift s C x).1 = (lift s C y).1 ↔ x.1 = y.1 :=
  (packetEquiv s C).injective.eq_iff

theorem parameter_symm (x y : Vertex I K) : parameter x y = parameter y x := mul_comm _ _

theorem chi_translate (g : K) (x : Vertex I K) (j : I) :
    chi (translate g x) j = g * chi x j := by simp [chi,translate,mul_assoc]

theorem parameter_translate_left (g : K) (x y : Vertex I K) :
    parameter (translate g x) y = g * parameter x y := by
  simp [parameter,chi,translate,mul_assoc]

theorem parameter_translate_right (g : K) (x y : Vertex I K) :
    parameter x (translate g y) = g * parameter x y := by
  rw [parameter_symm,parameter_translate_left,parameter_symm x y]

theorem vertex_card [Fintype I] [DecidableEq I] [Fintype K] :
    Fintype.card (Vertex I K) = Fintype.card I * Fintype.card K ^ (Fintype.card I + 1) := by
  simp [Vertex,Packet,Row,Fintype.card_prod,Fintype.card_fun,pow_succ,mul_assoc]

section Square
variable (hsquare : ∀ g : K, g * g = 1)
include hsquare

theorem chi_lift (s : Structural I K) (C : Matrix I K) (x : Vertex I K) (j : I) :
    chi (lift s C x) (s.sigma j) = chi x j * C x.1.1 j := by
  change (x.2 * s.offset x.1.1) * rowImage s C x.1.1 x.1.2 (s.sigma j) = _
  rw [rowImage_apply_sigma]
  calc
    _ = (x.2 * x.1.2 j * C x.1.1 j) * (s.offset x.1.1 * s.offset x.1.1) := by ac_rfl
    _ = _ := by rw [hsquare,mul_one]; rfl

theorem parameter_lift (s : Structural I K) (C : Matrix I K) (x y : Vertex I K) :
    parameter (lift s C x) (lift s C y) =
      parameter x y * (C x.1.1 y.1.1 * C y.1.1 x.1.1) := by
  change chi (lift s C x) (s.sigma y.1.1) * chi (lift s C y) (s.sigma x.1.1) = _
  rw [chi_lift hsquare,chi_lift hsquare]
  unfold parameter
  ac_rfl

/-- Same structural index causes cancellation, with NO condition on `C i i`. -/
theorem parameter_lift_same_index (s : Structural I K) (C : Matrix I K)
    (x y : Vertex I K) (hi : x.1.1 = y.1.1) :
    parameter (lift s C x) (lift s C y) = parameter x y := by
  rw [parameter_lift hsquare,hi,hsquare,mul_one]

theorem parameter_lift_unrecorded (s : Structural I K) (R : I → I → Prop)
    (C : Matrix I K) (hC : Legal R C) (x y : Vertex I K)
    (hi : x.1.1 ≠ y.1.1) (hr : ¬ R x.1.1 y.1.1) :
    parameter (lift s C x) (lift s C y) = parameter x y := by
  rw [parameter_lift hsquare,hC _ _ hi hr,hsquare,mul_one]

theorem diagonal_lift (g : K) (x : Vertex I K) :
    lift (⟨Equiv.refl I,fun _ => g⟩ : Structural I K) (fun _ _ => g) x = translate g x := by
  rcases x with ⟨⟨i,f⟩,z⟩
  have hf : rowImage (⟨Equiv.refl I,fun _ => g⟩ : Structural I K) (fun _ _ => g) i f = f := by
    funext j; simp [rowImage,hsquare]
  simp [lift,packetMap,hf,translate,mul_comm]

theorem lift_owner {B : Type w} [MulAction K B] (beta : I → B)
    (gamma : B → B) (hcomm : ∀ (g : K) (b : B), gamma (g • b) = g • gamma b)
    (s : Structural I K) (hbeta : ∀ i, beta (s.sigma i) = s.offset i • gamma (beta i))
    (C : Matrix I K) (x : Vertex I K) :
    (lift s C x).2 • beta (lift s C x).1.1 = gamma (x.2 • beta x.1.1) := by
  change (x.2 * s.offset x.1.1) • beta (s.sigma x.1.1) = _
  rw [hbeta,mul_smul,← mul_smul (s.offset x.1.1),hsquare,one_smul,hcomm]

end Square
end CCO.FullRows
