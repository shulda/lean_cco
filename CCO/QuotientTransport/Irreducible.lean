import CCO.QuotientTransport.Lattice

universe u v w
namespace CCO.QuotientTransport
variable {G : Type u} [Group G] {A : Type v} {B : Type w}
variable [MulAction G A] [MulAction G B]

def ProperMeetIrreducible (H : InvEq G A) : Prop :=
  H ≠ ⊤ ∧ ∀ L N : InvEq G A, H = L ⊓ N → H = L ∨ H = N

/-- The global definition and its upper-interval test agree: EVERY meet
factor already lies above H, and therefore above the interval bottom E. -/
theorem meetIrreducible_interval (E H : InvEq G A) (hEH : E ≤ H) :
    ProperMeetIrreducible H ↔
      H ≠ ⊤ ∧ ∀ L N : InvEq G A, E ≤ L → E ≤ N → H = L ⊓ N → H = L ∨ H = N := by
  constructor
  · rintro ⟨hp,hm⟩
    exact ⟨hp,fun L N _ _ h => hm L N h⟩
  · rintro ⟨hp,hm⟩
    refine ⟨hp,fun L N h => hm L N ?_ ?_ h⟩
    · exact hEH.trans (h ▸ inf_le_left)
    · exact hEH.trans (h ▸ inf_le_right)

namespace Transport
variable {E : InvEq G A} {R : Rel A B} (T : Transport E R)

theorem push_top : T.push ⊤ le_top = ⊤ := by
  apply InvEq.ext
  intro y z
  rw [InvEq.top_apply]
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨x,hx⟩ := T.coserial y
    obtain ⟨x',hx'⟩ := T.coserial z
    exact (T.push_iff _ _ y z).mpr ⟨x,x',hx,(InvEq.top_apply x x').mpr trivial,hx'⟩

theorem pull_inf (L N : InvEq G B) (hL : T.target ≤ L) (hN : T.target ≤ N) :
    T.pull (L ⊓ N) (le_inf hL hN) = T.pull L hL ⊓ T.pull N hN :=
  T.reverse.push_inf L N hL hN

theorem push_eq_iff {H K : InvEq G A} (hH : E ≤ H) (hK : E ≤ K) :
    T.push H hH = T.push K hK ↔ H = K := by
  constructor
  · intro h
    have he : T.intervalIso ⟨H,hH⟩ = T.intervalIso ⟨K,hK⟩ := Subtype.ext h
    exact congrArg Subtype.val (T.intervalIso.injective he)
  · rintro rfl; rfl

/-- C08: proper binary meet-irreducibility in the FULL invariant lattices. -/
theorem push_meetIrreducible (H : InvEq G A) (hH : E ≤ H) :
    ProperMeetIrreducible (T.push H hH) ↔ ProperMeetIrreducible H := by
  constructor
  · rintro ⟨hp,hm⟩
    refine ⟨fun h => hp (h ▸ T.push_top),fun L N h => ?_⟩
    have hL : E ≤ L := hH.trans (h ▸ inf_le_left)
    have hN : E ≤ N := hH.trans (h ▸ inf_le_right)
    have ht : T.push H hH = T.push L hL ⊓ T.push N hN := by
      rw [← T.push_inf L N hL hN]
      exact (T.push_eq_iff hH (le_inf hL hN)).mpr h
    rcases hm (T.push L hL) (T.push N hN) ht with he | he
    · exact Or.inl ((T.push_eq_iff hH hL).mp he)
    · exact Or.inr ((T.push_eq_iff hH hN).mp he)
  · rintro ⟨hp,hm⟩
    refine ⟨fun h => hp ((T.push_eq_iff hH le_top).mp (h.trans T.push_top.symm)),fun L N h => ?_⟩
    have hL : T.target ≤ L := (T.target_le_push H hH).trans (h ▸ inf_le_left)
    have hN : T.target ≤ N := (T.target_le_push H hH).trans (h ▸ inf_le_right)
    have ht : H = T.pull L hL ⊓ T.pull N hN := by
      rw [← T.pull_inf L N hL hN,← T.pull_push H hH]
      congr 1
    rcases hm (T.pull L hL) (T.pull N hN) ht with he | he
    · left
      calc
        T.push H hH = T.push (T.pull L hL) (T.source_le_pull L hL) :=
          (T.push_eq_iff hH (T.source_le_pull L hL)).mpr he
        _ = L := T.push_pull L hL
    · right
      calc
        T.push H hH = T.push (T.pull N hN) (T.source_le_pull N hN) :=
          (T.push_eq_iff hH (T.source_le_pull N hN)).mpr he
        _ = N := T.push_pull N hN
end Transport
end CCO.QuotientTransport
