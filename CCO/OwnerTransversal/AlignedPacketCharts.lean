import CCO.OwnerTransversal.PacketCharts
import Mathlib.Data.Set.Finite.Basic

/-! A regular packet chart can use prescribed actual origins. On every
packet meeting an invariant protected set, the chosen origin is an actual
protected preimage of phase ZERO, obtained by inverse translation of its
point image. Owner labels alone do not choose this origin. -/

universe u v w z
namespace CCO.OwnerTransversal.PacketCoordinates.RegularPackets
noncomputable section

variable {K : Type u} [Group K] {P : Type v} [MulAction K P] {I : Type w}
variable (D : RegularPackets (K := K) (P := P) (I := I))

def coordinatesWith (o : I → P) (ho : ∀ i, D.packet (o i) = i) : P ≃ I × K :=
  (Equiv.ofBijective (fun p : I × K => p.2 • o p.1) (by
    constructor
    · rintro ⟨i,g⟩ ⟨j,h⟩ he
      have hij : i = j := by
        simpa only [D.invariant,ho] using congrArg D.packet he
      subst j
      have hgh : g = h := by
        obtain ⟨k,hk,hunique⟩ := D.regular (o i) (g • o i) (D.invariant g (o i)).symm
        exact (hunique g rfl).trans (hunique h he.symm).symm
      exact Prod.ext rfl hgh
    · intro p
      obtain ⟨g,hg,_⟩ := D.regular (o (D.packet p)) p (ho _)
      exact ⟨(D.packet p,g),hg⟩)).symm

@[simp] theorem coordinatesWith_symm (o : I → P) (ho : ∀ i, D.packet (o i) = i)
    (i : I) (g : K) : (D.coordinatesWith o ho).symm (i,g) = g • o i := rfl

theorem coordinatesWith_fst (o : I → P) (ho : ∀ i, D.packet (o i) = i) (p : P) :
    ((D.coordinatesWith o ho) p).1 = D.packet p := by
  have hp := congrArg D.packet ((D.coordinatesWith o ho).symm_apply_apply p)
  change D.packet (((D.coordinatesWith o ho) p).2 • o ((D.coordinatesWith o ho) p).1) =
    D.packet p at hp
  simpa only [D.invariant,ho] using hp

theorem coordinatesWith_action (o : I → P) (ho : ∀ i, D.packet (o i) = i)
    (g : K) (p : P) :
    (D.coordinatesWith o ho) (g • p) =
      (((D.coordinatesWith o ho) p).1,g * ((D.coordinatesWith o ho) p).2) := by
  apply (D.coordinatesWith o ho).symm.injective
  rw [Equiv.symm_apply_apply,coordinatesWith_symm]
  have hp := (D.coordinatesWith o ho).symm_apply_apply p
  change ((D.coordinatesWith o ho) p).2 • o ((D.coordinatesWith o ho) p).1 = p at hp
  rw [mul_smul,hp]

include D in
theorem finite_indices [Finite P] : Finite I := Finite.of_surjective D.packet D.onto

variable (A : Set P) [MulAction K ↥A] {U : Type z}
variable (inclusion : ∀ (g : K) (a : ↥A), (g • a).val = g • a.val)
variable (f : ↥A → U × K)
variable (equivariant : ∀ (g : K) a, f (g • a) = ((f a).1,g * (f a).2))

def anchoredOrigin (i : I) : P := by
  classical
  exact if h : ∃ a : ↥A, D.packet a.val = i then
    (alignedOrigin f h.choose).val else D.origin i

include inclusion in
theorem packet_anchoredOrigin (i : I) :
    D.packet (D.anchoredOrigin A f i) = i := by
  classical
  by_cases h : ∃ a : ↥A, D.packet a.val = i
  · rw [anchoredOrigin,dite_eq_left h]
    change D.packet (((f h.choose).2⁻¹ • h.choose).val) = i
    rw [inclusion,D.invariant]
    exact h.choose_spec
  · rw [anchoredOrigin,dite_eq_right h,D.packet_origin]

include equivariant in
/-- The selected origin is a REAL protected point mapping to phase zero. -/
theorem anchoredOrigin_protected {i : I} (h : ∃ a : ↥A, D.packet a.val = i) :
    ∃ a : ↥A, a.val = D.anchoredOrigin A f i ∧ (f a).2 = 1 := by
  refine ⟨alignedOrigin f h.choose,?_,?_⟩
  · simp only [anchoredOrigin,dite_eq_left h]
  · exact congrArg Prod.snd (alignedOrigin_image f equivariant h.choose)

def anchoredCoordinates : P ≃ I × K :=
  D.coordinatesWith (D.anchoredOrigin A f) (D.packet_anchoredOrigin A inclusion f)

theorem anchoredCoordinates_fst (p : P) :
    ((D.anchoredCoordinates A inclusion f) p).1 = D.packet p :=
  D.coordinatesWith_fst _ _ p

theorem anchoredCoordinates_action (g : K) (p : P) :
    (D.anchoredCoordinates A inclusion f) (g • p) =
      (((D.anchoredCoordinates A inclusion f) p).1,
        g * ((D.anchoredCoordinates A inclusion f) p).2) :=
  D.coordinatesWith_action _ _ g p

include equivariant in
/-- On the entire protected set, the constructed chart's phase equals
the actual point-image phase, even if its owner action has stabilizers. -/
theorem anchoredCoordinates_phase (a : ↥A) :
    ((D.anchoredCoordinates A inclusion f) a.val).2 = (f a).2 := by
  let c := D.anchoredCoordinates A inclusion f
  obtain ⟨a₀,ha₀,hzero⟩ := D.anchoredOrigin_protected A f equivariant
    (i := D.packet a.val) ⟨a,rfl⟩
  have hfst : (c a.val).1 = D.packet a.val := D.anchoredCoordinates_fst A inclusion f a.val
  have hp : (c a.val).2 • D.anchoredOrigin A f (D.packet a.val) = a.val := by
    have h := c.symm_apply_apply a.val
    change (c a.val).2 • D.anchoredOrigin A f (c a.val).1 = a.val at h
    simpa only [hfst] using h
  have he : (c a.val).2 • a₀ = a := by
    apply Subtype.ext
    rw [inclusion,ha₀]
    exact hp
  have hf := congrArg Prod.snd (equivariant (c a.val).2 a₀)
  rw [he,hzero,mul_one] at hf
  exact hf.symm

end
end CCO.OwnerTransversal.PacketCoordinates.RegularPackets
