import CCO.OwnerTransversal.PacketCoordinates

/-! A literal partition into regular packets admits full coordinates.
Origins and the chart are constructed by choice; no canonical or
equivariant choice of origins is claimed. -/
universe u v w
namespace CCO.OwnerTransversal.PacketCoordinates
noncomputable section
variable {K : Type u} [Group K] {P : Type v} [MulAction K P] {I : Type w}

structure RegularPackets where
  packet : P → I
  onto : Function.Surjective packet
  invariant : ∀ (g : K) p, packet (g • p) = packet p
  regular : ∀ p q, packet p = packet q → ∃! g : K, g • p = q

namespace RegularPackets
variable (D : RegularPackets (K := K) (P := P) (I := I))

def origin (i : I) : P := (D.onto i).choose

@[simp] theorem packet_origin (i : I) : D.packet (D.origin i) = i := (D.onto i).choose_spec

def coordinates : P ≃ I × K := (Equiv.ofBijective
    (fun p : I × K => p.2 • D.origin p.1) (by
      constructor
      · rintro ⟨i,g⟩ ⟨j,h⟩ he
        have hij : i = j := by
          simpa only [D.invariant,D.packet_origin] using congrArg D.packet he
        subst j
        have hgh : g = h := by
          obtain ⟨k,hk,hunique⟩ := D.regular (D.origin i) (g • D.origin i)
            (D.invariant g (D.origin i)).symm
          exact (hunique g rfl).trans (hunique h he.symm).symm
        exact Prod.ext rfl hgh
      · intro p
        obtain ⟨g,hg,_⟩ := D.regular (D.origin (D.packet p)) p (D.packet_origin _)
        exact ⟨(D.packet p,g),hg⟩)).symm

@[simp] theorem coordinates_symm (i : I) (g : K) :
    D.coordinates.symm (i,g) = g • D.origin i := rfl

theorem coordinates_action (g : K) (p : P) :
    D.coordinates (g • p) = ((D.coordinates p).1,g * (D.coordinates p).2) := by
  apply D.coordinates.symm.injective
  rw [Equiv.symm_apply_apply,coordinates_symm]
  have hp := D.coordinates.symm_apply_apply p
  change (D.coordinates p).2 • D.origin (D.coordinates p).1 = p at hp
  rw [mul_smul,hp]

theorem coordinates_fst (p : P) : (D.coordinates p).1 = D.packet p := by
  have hp := congrArg D.packet (D.coordinates.symm_apply_apply p)
  change D.packet ((D.coordinates p).2 • D.origin (D.coordinates p).1) = D.packet p at hp
  simpa only [D.invariant,D.packet_origin] using hp

end RegularPackets
end
end CCO.OwnerTransversal.PacketCoordinates
