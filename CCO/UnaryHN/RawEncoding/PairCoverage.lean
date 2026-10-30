import CCO.UnaryHN.RawEncoding.Free
import Lean.Elab.Tactic.Omega

/-! Unary reachability or a POSITIVE binary tuple prevents a proper closed
free split. Extra relation symbols of arbitrary arity are harmless. -/
universe u v
namespace CCO.UnaryHN.Raw
open CCO.UnarySupport (Signature)
variable {L : Signature.{u}} {V : Type v} (C : Typed L V)

def BinaryEdge (x y : V) : Prop :=
  ∃ (R : L.Rel) (_ : L.arity R = 2),
    C.rel R (fun i => if i.val = 0 then x else y)

def PairCoverage : Prop :=
  ∀ x y, x ≠ y → x ∈ C.closure {y} ∨ y ∈ C.closure {x} ∨
    BinaryEdge C x y ∨ BinaryEdge C y x

theorem unary_link_reachable (F : L.Func) (x y : V) (hy : y ∈ C.func F x) :
    y ∈ C.closure {x} :=
  ⟨x, rfl, Relation.ReflTransGen.tail Relation.ReflTransGen.refl ⟨F, hy⟩⟩

theorem irreducible_of_pairCoverage (hCover : PairCoverage C) : C.Irreducible := by
  classical
  constructor
  intro d
  have exL : ∃ x, x ∉ d.left := by
    by_contra h
    apply d.left_proper
    exact Set.eq_univ_of_forall (fun x => by simpa using not_exists.mp h x)
  have exR : ∃ y, y ∉ d.right := by
    by_contra h
    apply d.right_proper
    exact Set.eq_univ_of_forall (fun y => by simpa using not_exists.mp h y)
  obtain ⟨x, hx⟩ := exL
  obtain ⟨y, hy⟩ := exR
  have cover (z : V) : z ∈ d.left ∨ z ∈ d.right := by
    rw [← Set.mem_union, d.cover]
    trivial
  have hxR : x ∈ d.right := (cover x).resolve_left hx
  have hyL : y ∈ d.left := (cover y).resolve_right hy
  have hxy : x ≠ y := by intro h; exact hx (h ▸ hyL)
  rcases hCover x y hxy with hReach | hReach | hEdge | hEdge
  · exact hx (C.closure_minimal d.left_closed (by intro z hz; simp only [Set.mem_singleton_iff] at hz; exact hz ▸ hyL) hReach)
  · exact hy (C.closure_minimal d.right_closed (by intro z hz; simp only [Set.mem_singleton_iff] at hz; exact hz ▸ hxR) hReach)
  · obtain ⟨R, hR, hRel⟩ := hEdge
    let i0 : Fin (L.arity R) := ⟨0, by omega⟩
    let i1 : Fin (L.arity R) := ⟨1, by omega⟩
    rcases d.rel_local R _ hRel with hl | hr
    · exact hx (by simpa [i0] using hl i0)
    · exact hy (by simpa [i1] using hr i1)
  · obtain ⟨R, hR, hRel⟩ := hEdge
    let i0 : Fin (L.arity R) := ⟨0, by omega⟩
    let i1 : Fin (L.arity R) := ⟨1, by omega⟩
    rcases d.rel_local R _ hRel with hl | hr
    · exact hx (by simpa [i1] using hl i1)
    · exact hy (by simpa [i0] using hr i0)

/-- C01: retain the source's totality premise, although closedness suffices. -/
theorem typed_unary_binary_irreducibility (_hTotal : C.Total) (hCover : PairCoverage C) :
    C.Irreducible := irreducible_of_pairCoverage C hCover

/-- C02: positive binary coverage supplies the third three-way alternative. -/
theorem binary_coverage_irreducible (_hTotal : C.Total)
    (hBinary : ∀ x y, x ≠ y → BinaryEdge C x y) : C.Irreducible :=
  irreducible_of_pairCoverage C (fun x y h => Or.inr (Or.inr (Or.inl (hBinary x y h))))

end CCO.UnaryHN.Raw
