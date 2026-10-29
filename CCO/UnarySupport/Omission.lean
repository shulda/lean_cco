import CCO.UnarySupport.Supports

universe u v
namespace CCO.UnarySupport.Structure
variable {L : Signature.{u}} {V : Type v} (C : Structure L V)

def omission (y : V) : Set V := ⋃₀ {S | C.LocalSupport S ∧ y ∉ S}

theorem omission_closed (y : V) : C.IsClosed (C.omission y) :=
  C.isClosed_sUnion (fun _ h => C.localSupport_closed h.1)

theorem not_mem_omission (y : V) : y ∉ C.omission y := by
  rintro ⟨S, hS, hy⟩
  exact hS.2 hy

theorem omission_pair (x y : V) (hno : ¬ ∃ S, C.LocalSupport S ∧ x ∈ S ∧ y ∈ S) :
    x ∈ C.omission y ∧ y ∈ C.omission x := by
  constructor
  · refine ⟨C.closureAt x, ⟨.singleton x, ?_⟩, C.mem_closureAt x⟩
    intro hy
    exact hno ⟨_, .singleton x, C.mem_closureAt x, hy⟩
  · refine ⟨C.closureAt y, ⟨.singleton y, ?_⟩, C.mem_closureAt y⟩
    intro hx
    exact hno ⟨_, .singleton y, hx, C.mem_closureAt y⟩

theorem support_omission_side (x y : V)
    (hno : ¬ ∃ S, C.LocalSupport S ∧ x ∈ S ∧ y ∈ S)
    {S : Set V} (hS : C.LocalSupport S) :
    S ⊆ C.omission y ∨ S ⊆ C.omission x := by
  classical
  by_cases hy : y ∈ S
  · right
    have hx : x ∉ S := fun hx => hno ⟨S, hS, hx, hy⟩
    exact fun z hz => ⟨S, ⟨hS, hx⟩, hz⟩
  · left
    exact fun z hz => ⟨S, ⟨hS, hy⟩, hz⟩

theorem omission_cover (x y : V)
    (hno : ¬ ∃ S, C.LocalSupport S ∧ x ∈ S ∧ y ∈ S) :
    C.omission y ∪ C.omission x = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨S, hS, hz⟩ := C.point_support z
  rcases C.support_omission_side x y hno hS with hl | hr
  · exact Or.inl (hl hz)
  · exact Or.inr (hr hz)

/-- The actual two induced closed factors, including the entire possibly
empty overlap, have exactly the ambient relation and partial-function union. -/
def omissionDecomposition (hbin : ∀ R, L.arity R ≤ 2) (x y : V)
    (hno : ¬ ∃ S, C.LocalSupport S ∧ x ∈ S ∧ y ∈ S) : C.FreeDecomposition where
  left := C.omission y
  right := C.omission x
  left_closed := C.omission_closed y
  right_closed := C.omission_closed x
  cover := C.omission_cover x y hno
  left_proper he := C.not_mem_omission y (he ▸ Set.mem_univ y)
  right_proper he := C.not_mem_omission x (he ▸ Set.mem_univ x)
  rel_local R xs hr := by
    by_cases hn : 0 < L.arity R
    · obtain ⟨S, hS, hxs⟩ := C.tuple_support hbin R xs hr hn
      rcases C.support_omission_side x y hno hS with hl | hr
      · exact Or.inl (fun i => hl (hxs i))
      · exact Or.inr (fun i => hr (hxs i))
    · left
      intro i
      exact False.elim (hn (Nat.zero_lt_of_lt i.isLt))

theorem pair_support (hbin : ∀ R, L.arity R ≤ 2) (hirr : C.Irreducible)
    (x y : V) (_hxy : x ≠ y) : ∃ S, C.LocalSupport S ∧ x ∈ S ∧ y ∈ S := by
  classical
  by_contra hno
  exact hirr.false (C.omissionDecomposition hbin x y hno)

end CCO.UnarySupport.Structure
