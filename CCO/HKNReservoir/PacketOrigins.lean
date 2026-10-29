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


theorem origin_mem_closure (x : W) : origin tag D E hLocal hD (packet E x) ∈ E.closureAtSet x := by
  have hc := (packet_eq E _ _).mp (packet_origin tag D E hLocal hD (packet E x))
  exact hc ▸ E.mem_closureAtSet (origin tag D E hLocal hD (packet E x))

theorem origin_injective : Function.Injective (origin tag D E hLocal hD) := by
  intro i j he
  exact (packet_origin tag D E hLocal hD i).symm.trans
    ((congrArg (packet E) he).trans (packet_origin tag D E hLocal hD j))

/-- Any recorded cross edge forces a record on the chosen origins of the
SAME two packets, by exact reflection of their whole closed union. -/
theorem origin_record_of_record (hFine : FineData D) (x y : W) (a : Atom)
    (ha : E.rel (.fine a) (![x,y])) (hne : packet E x ≠ packet E y) :
    ∃ c, originEdge tag D E hLocal hD (packet E x) (packet E y) = some c := by
  let ox := origin tag D E hLocal hD (packet E x)
  let oy := origin tag D E hLocal hD (packet E y)
  let p : pairSet E x y := ⟨ox,Or.inl (origin_mem_closure tag D E hLocal hD x)⟩
  let q : pairSet E x y := ⟨oy,Or.inr (origin_mem_closure tag D E hLocal hD y)⟩
  let e := pairEmbedding tag D E hLocal x y a ha
  have ho : ox ≠ oy := fun he => hne (origin_injective tag D E hLocal hD he)
  have he : e p ≠ e q := fun h => ho (congrArg Subtype.val (e.injective h))
  obtain ⟨c,hc⟩ := hFine.complete (e p) (e q) he
  exact ⟨c,(originEdge_some tag D E hLocal hD hFine _ _ c).mpr
    ((embedding_fine tag D E (pair_closed E x y) e c p q).mpr hc)⟩

instance finite_packetIndex [Finite W] : Finite (PacketIndex E) :=
  Finite.of_surjective (packet E) Quotient.mk_surjective

end PacketRecovery
end CCO.HKNReservoir
