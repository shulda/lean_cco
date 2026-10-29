import CCO.HKNReservoir.PacketMatrices
import CCO.OwnerTransversal.PacketCharts

universe u v w z x y
namespace CCO.HKNReservoir
open AllThoseEPPA
variable {B : Type u} {K : Type v} [Group K] {Atom : Type w}
variable {V : Type x} {W : Type y} {Γ : Type z} [Group Γ]
namespace PacketRecovery
variable (tag : Γ →* Equiv.Perm B) (D : Data B K Atom V)
variable (E : Structure (Signature B K Atom) W)
variable (hLocal : LocallyInSource tag (encode D) E) (hD : RegularData D)

def closureSetoid : Setoid W where
  r x y := E.closureAtSet x = E.closureAtSet y
  iseqv := ⟨fun _ => rfl,Eq.symm,Eq.trans⟩

abbrev PacketIndex := Quotient (closureSetoid E)
def packet (x : W) : PacketIndex E := Quotient.mk _ x

theorem packet_eq (x y : W) : packet E x = packet E y ↔ E.closureAtSet x = E.closureAtSet y :=
  ⟨fun h => Quotient.exact h,fun h => @Quotient.sound _ (closureSetoid E) x y h⟩

noncomputable def packets :
    letI := PacketRecovery.action tag D E hLocal hD
    OwnerTransversal.PacketCoordinates.RegularPackets (K:=K) (P:=W) (I:=PacketIndex E) := by
  letI := PacketRecovery.action tag D E hLocal hD
  refine { packet := packet E, onto := Quotient.mk_surjective, invariant := ?_, regular := ?_ }
  · intro g x
    apply Quotient.sound
    change E.closureAtSet (move tag D E hLocal g x) = E.closureAtSet x
    rw [closure_eq_orbit tag D E hLocal hD,closure_eq_orbit tag D E hLocal hD,orbit_move tag D E hLocal hD]
  · intro x y hxy
    have hc : E.closureAtSet x = E.closureAtSet y := Quotient.exact hxy
    have hy : y ∈ E.closureAtSet x := hc.symm ▸ E.mem_closureAtSet y
    have ho : y ∈ orbit tag D E hLocal x := (closure_eq_orbit tag D E hLocal hD x) ▸ hy
    obtain ⟨g,hg⟩ := ho
    exact ⟨g,hg,fun h hh => move_free tag D E hLocal hD x (hh.trans hg.symm)⟩

/-- One arbitrary origin in each actual recovered packet, with no
canonical or equivariant choice asserted. -/
noncomputable def origin (i : PacketIndex E) : W := by
  letI := PacketRecovery.action tag D E hLocal hD
  exact (packets tag D E hLocal hD).origin i

theorem packet_origin (i : PacketIndex E) : packet E (origin tag D E hLocal hD i) = i := by
  letI := PacketRecovery.action tag D E hLocal hD
  exact (packets tag D E hLocal hD).packet_origin i

noncomputable def originOwner (i : PacketIndex E) : B := owner tag D E hLocal (origin tag D E hLocal hD i)

noncomputable def originEdge (i j : PacketIndex E) : Option Atom := by
  classical
  exact if h : ∃ a, E.rel (.fine a) (![origin tag D E hLocal hD i,origin tag D E hLocal hD j])
    then some h.choose else none

theorem originEdge_some (hFine : FineData D) (i j : PacketIndex E) (a : Atom) :
    originEdge tag D E hLocal hD i j = some a ↔
      E.rel (.fine a) (![origin tag D E hLocal hD i,origin tag D E hLocal hD j]) := by
  classical
  by_cases h : ∃ b, E.rel (.fine b) (![origin tag D E hLocal hD i,origin tag D E hLocal hD j])
  · simp only [originEdge,dif_pos h,Option.some.injEq]
    constructor
    · rintro rfl; exact h.choose_spec
    · intro ha
      exact fine_unique tag D E hLocal hFine _ _ _ _ h.choose_spec ha
  · simp only [originEdge,dif_neg h]
    constructor
    · intro he; cases he
    · intro ha; exact (h ⟨a,ha⟩).elim

theorem originEdge_symmetric (hFine : FineData D) (i j : PacketIndex E) :
    originEdge tag D E hLocal hD i j = originEdge tag D E hLocal hD j i := by
  cases he : originEdge tag D E hLocal hD i j with
  | none =>
    cases hf : originEdge tag D E hLocal hD j i with
    | none => rfl
    | some a =>
      have ha := fine_symmetric tag D E hLocal hFine _ _ a ((originEdge_some tag D E hLocal hD hFine j i a).mp hf)
      have hh := (originEdge_some tag D E hLocal hD hFine i j a).mpr ha
      rw [he] at hh; cases hh
  | some a =>
    exact ((originEdge_some tag D E hLocal hD hFine j i a).mpr
      (fine_symmetric tag D E hLocal hFine _ _ a ((originEdge_some tag D E hLocal hD hFine i j a).mp he))).symm

theorem originEdge_diagonal (hFine : FineData D) (i : PacketIndex E) :
    originEdge tag D E hLocal hD i i = none := by
  classical
  have hn : ¬∃ a, E.rel (.fine a) (![origin tag D E hLocal hD i,origin tag D E hLocal hD i]) := by
    rintro ⟨a,ha⟩
    exact fine_irreflexive tag D E hLocal hFine _ a ha
  simp only [originEdge,dif_neg hn]

theorem origin_closures_distinct {i j : PacketIndex E} (hij : i ≠ j) :
    E.closureAtSet (origin tag D E hLocal hD i) ≠ E.closureAtSet (origin tag D E hLocal hD j) := by
  intro he
  exact hij ((packet_origin tag D E hLocal hD i).symm.trans
    ((Quotient.sound he).trans (packet_origin tag D E hLocal hD j)))

end PacketRecovery
end CCO.HKNReservoir
