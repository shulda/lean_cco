import CCO.TypedOrbitFrames.CellBoundary
import CCO.TypedOrbitFrames.CoarseBlockBoundary
import CCO.UnaryFreshFrames.Age
import Mathlib.Tactic.FinCases

/-!
# Source12 signature boundaries

These are actual infinite named models and their finite closed pieces.
They are not extra source12 exports and are not inputs to the hereditary
orbit theorem. In particular, hidden SAP additionally needs the separate
homogeneity hypothesis of the accepted generic criterion.
-/

namespace CCO.HereditaryHiddenOrbits.Boundaries
open CCO.UnaryFreshFrames
namespace Cell
open CCO.TypedOrbitFrames.CellBoundary

/-- C23: BOTH orphan parameters determine a non-MI cell outside their
literal unary closure. Each single orphan still has an infinite cell orbit. -/
theorem orphan_cell_boundary (r c : Nat) :
    cell r c ∈ Dcl model.Aut (orphanBase r c) ∧
    cell r c ∈ Acl model.Aut (orphanBase r c) ∧
    cell r c ∉ model.closure (orphanBase r c) ∧
    (orbitOver model.Aut {row r} (cell r c)).Infinite ∧
    (orbitOver model.Aut {column c} (cell r c)).Infinite ∧
    ¬ InfIrred cellKernel := by
  obtain ⟨hd,ha,hn⟩ := cell_algebraic_outside_unary_closure r c
  exact ⟨hd,ha,hn,cell_orbit_over_one_row_infinite r c,
    cell_orbit_over_one_column_infinite r c,cell_kernel_not_meet_irreducible⟩

/-- The forbidden extra coordinate is nevertheless proper, nonidentity
and equality-inclusive RAW exact; exactness alone cannot replace MI. -/
theorem exact_non_mi_kernel_boundary :
    cellKernel ≠ ⊥ ∧ cellKernel ≠ ⊤ ∧ ¬ InfIrred cellKernel ∧
    ∀ x y : Real, cellKernel x y ↔
      ∃ z : Real, sameCellDiversity x z ∧ sameCellDiversity z y :=
  ⟨cell_kernel_nonidentity,cell_kernel_proper,
    cell_kernel_not_meet_irreducible,cell_kernel_raw_square⟩

def realHull (r c n : Nat) : Set Point :=
  {real r c n,row r,column c,cell r c}

theorem realHull_closed (r c n : Nat) : model.Closed (realHull r c n) := by
  intro F x hx
  rcases hx with rfl | rfl | rfl | rfl
  all_goals fin_cases F <;> simp [realHull,model,operation,real,row,column,cell]

/-- C24: the same cross-cell obstruction already occurs over TWO actual
real generators. Their unary hull contains only their own cells. -/
theorem real_generated_cross_cell (r c r0 c0 n0 n1 : Nat)
    (hr : r ≠ r0) (hc : c ≠ c0) :
    cell r c ∈ Dcl model.Aut {real r c0 n0,real r0 c n1} ∧
    cell r c ∈ Acl model.Aut {real r c0 n0,real r0 c n1} ∧
    cell r c ∉ model.closure {real r c0 n0,real r0 c n1} := by
  have hd : cell r c ∈ Dcl model.Aut {real r c0 n0,real r0 c n1} := by
    intro g
    apply cell_fixed_by_full_aut r c g.val
    · have he := model.aut_func g.val 0 (real r c0 n0)
      rw [g.property (real r c0 n0) (Or.inl rfl)] at he
      exact he
    · have he := model.aut_func g.val 1 (real r0 c n1)
      rw [g.property (real r0 c n1) (Or.inr rfl)] at he
      exact he
  refine ⟨hd,dcl_subset_acl model.Aut _ hd,?_⟩
  have hHull : model.closure {real r c0 n0,real r0 c n1} ⊆
      realHull r c0 n0 ∪ realHull r0 c n1 := by
    apply model.closure_minimal (model.closed_union
      (realHull_closed r c0 n0) (realHull_closed r0 c n1))
    rintro x (rfl | rfl) <;> simp [realHull]
  intro h
  have h' := hHull h
  simp [realHull,real,row,column,cell,hc,hr] at h'

def extension (r c : Nat) : Set Point := orphanBase r c ∪ {cell r c}

theorem extension_closed (r c : Nat) : model.Closed (extension r c) := by
  intro F x hx
  rcases hx with hx | rfl
  · exact Or.inl (orphan_base_closed r c F x hx)
  · fin_cases F <;> simp [extension,orphanBase,model,operation,row,column,cell]

def basePiece (r c : Nat) : model.Piece :=
  ⟨orphanBase r c,orphan_base_finite r c,orphan_base_closed r c⟩

def extensionPiece (r c : Nat) : model.Piece :=
  ⟨extension r c,(orphan_base_finite r c).union (Set.finite_singleton _),
    extension_closed r c⟩

theorem cell_projections_injective (x y : Point) (hx : sort x = 3)
    (hy : sort y = 3) (hRow : operation 3 x = operation 3 y)
    (hColumn : operation 4 x = operation 4 y) : x = y := by
  rcases x with ⟨⟨r,c⟩,n⟩ | (r | (c | ⟨r,c⟩)) <;>
    rcases y with ⟨⟨r',c'⟩,n'⟩ | (r' | (c' | ⟨r',c'⟩)) <;>
    simp_all [sort,operation,row,column]

/-- C25: two copies of the finite CLOSED cell extension cannot be
strongly amalgamated. This direct age argument assumes no homogeneity. -/
theorem non_mi_cell_not_ageSAP : ¬ model.AgeSAP := by
  intro hsap
  let A := basePiece 0 0
  let B := extensionPiece 0 0
  let e : A.Embedding B.points := Structure.Piece.Embedding.inclusion
    (fun _ hx => Or.inl hx)
  obtain ⟨D,l,r,commute,strong⟩ := hsap A B B e e
  let b : B.points := ⟨cell 0 0,Or.inr rfl⟩
  have sameFunc (F : Fin 5) (a : A.points)
      (h : operation F (cell 0 0) = a.val) :
      operation F (l.point b) = operation F (r.point b) := by
    have hl := l.func_eq F b
    have hr := r.func_eq F b
    have hbl : B.func F b = ⟨e.point a,e.mem_point a⟩ := Subtype.ext h
    rw [hbl] at hl hr
    exact hl.symm.trans ((commute a).trans hr)
  have heq : l.point b = r.point b := by
    apply cell_projections_injective _ _ (l.sort_eq b) (r.sort_eq b)
    · exact sameFunc 3 ⟨row 0,Or.inl rfl⟩ rfl
    · exact sameFunc 4 ⟨column 0,Or.inr rfl⟩ rfl
  obtain ⟨a,ha,_⟩ := strong b b heq
  change a.val = cell 0 0 at ha
  have hcell : cell 0 0 ∈ orphanBase 0 0 := ha ▸ a.property
  simp [orphanBase,row,column,cell] at hcell

end Cell

namespace Cover
open CCO.TypedOrbitFrames.CoarseBlockBoundary

open CCO.UnaryFreshFrames.Examples.TwoCover in
/-- The actual FULL original-signature stabilizer orbit consists of the
TWO fine quotient vertices, so the bit swap is present in the full action. -/
theorem actual_fine_orbit_two (q : Nat) (b : Bool) :
    orbitOver originalModel.Aut {rootPoint q} (middle q b) =
      {middle q false,middle q true} := by
  change orbitOver originalModel.automorphisms {rootPoint q} (middle q b) = _
  rw [automorphisms_eq,full_middle_orbit]

/-- C26: in the actual fine signature the two points of a coarse fibre
are algebraic and lie outside the coarse orphan's named unary closure. -/
theorem fine_cover_boundary (q : Nat) (b : Bool) :
    CCO.UnaryFreshFrames.Examples.TwoCover.middle q b ∈ Acl CCO.UnaryFreshFrames.Examples.TwoCover.originalModel.Aut {CCO.UnaryFreshFrames.Examples.TwoCover.rootPoint q} ∧
    CCO.UnaryFreshFrames.Examples.TwoCover.middle q b ∉ CCO.UnaryFreshFrames.Examples.TwoCover.originalModel.closureAt (CCO.UnaryFreshFrames.Examples.TwoCover.rootPoint q) ∧
    ¬ CCO.UnaryFreshFrames.Examples.TwoCover.originalModel.AgeSAP := by
  obtain ⟨ha,hn⟩ := CCO.UnaryFreshFrames.Examples.TwoCover.original_algebraic_off_closure q b
  exact ⟨ha,hn,CCO.UnaryFreshFrames.Examples.TwoCover.original_not_ageSAP⟩

/-- C27: the smaller coarse signature has all existing unforced term
fibres infinite, whereas naming the fine projection exposes index TWO. -/
theorem coarse_fine_signature_difference (q : Nat) :
    (∀ {k : language.Sorts} (t : Term language false k),
      ¬ Quotient.KernelLe block (fun x : Real => model.eval t (.inl x)) →
      (Quotient.FibreValues block (fun x : Real => model.eval t (.inl x)) q).Infinite) ∧
    ¬ Quotient.KernelLe block fine ∧
    (Quotient.FibreValues block fine q).ncard = 2 :=
  ⟨fun t h => coarse_infinite_unforced_indices t h q,
    fine_unforced_for_coarse,fine_actual_relative_index_two q⟩

end Cover

namespace Hierarchical

abbrev Real := ((Nat × Nat) × Nat) × Nat
abbrev Point := Real ⊕ ((Nat × Nat) ⊕ ((Nat × Nat) ⊕ Nat))

def rowOf (x : Real) : Nat × Nat := x.1.1
def columnOf (x : Real) : Nat × Nat := (x.1.1.1,x.1.2)

def real (p r c n : Nat) : Point := .inl (((p,r),c),n)
def row (p r : Nat) : Point := .inr (.inl (p,r))
def column (p c : Nat) : Point := .inr (.inr (.inl (p,c)))
def parent (p : Nat) : Point := .inr (.inr (.inr p))

def sort : Point → Fin 4
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

abbrev language : Language where
  Sorts := Fin 4
  Func := Fin 5
  Rel := PEmpty
  input F := if F < 3 then 0 else if F = 3 then 1 else 2
  output F := if F = 0 then 1 else if F = 1 then 2 else 3
  arity := PEmpty.elim
  argument R := PEmpty.elim R

/-- The actual five unary maps name real row/column/parent values and
the two upward maps to the parent. Every off-sort value is the identity. -/
def operation (F : Fin 5) : Point → Point
  | .inl x =>
    if F = 0 then row x.1.1.1 x.1.1.2
    else if F = 1 then column x.1.1.1 x.1.2
    else if F = 2 then parent x.1.1.1 else .inl x
  | .inr (.inl x) => if F = 3 then parent x.1 else row x.1 x.2
  | .inr (.inr (.inl x)) => if F = 4 then parent x.1 else column x.1 x.2
  | .inr (.inr (.inr p)) => parent p

def model : Structure language Point where
  sort := sort
  func := operation
  func_sort := by
    intro F x hx
    fin_cases F <;>
      rcases x with ⟨⟨⟨p,r⟩,c⟩,n⟩ | (⟨p,r⟩ | (⟨p,c⟩ | p)) <;>
      simp_all [language,sort,operation,row,column,parent]
  func_offsort := by
    intro F x hx
    fin_cases F <;>
      rcases x with ⟨⟨⟨p,r⟩,c⟩,n⟩ | (⟨p,r⟩ | (⟨p,c⟩ | p)) <;>
      simp_all [language,sort,operation,row,column,parent]
  rel R := PEmpty.elim R
  rel_sort R := PEmpty.elim R

/-- C28: the upward names impose actual parent compatibility. -/
theorem actual_parent_maps (p r c n : Nat) :
    operation 0 (real p r c n) = row p r ∧
    operation 1 (real p r c n) = column p c ∧
    operation 2 (real p r c n) = parent p ∧
    operation 3 (row p r) = parent p ∧
    operation 4 (column p c) = parent p := ⟨rfl,rfl,rfl,rfl,rfl⟩

def fibre (a b : Nat × Nat) : Set Real :=
  {x | rowOf x = a ∧ columnOf x = b}

/-- Classes over DIFFERENT parents have no common original real point. -/
theorem incompatible_parents (a b : Nat × Nat) (h : a.1 ≠ b.1) :
    fibre a b = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨ha,hb⟩
  rcases x with ⟨⟨⟨p,r⟩,c⟩,n⟩
  change (p,r) = a at ha
  change (p,c) = b at hb
  have ha' : p = a.1 := congrArg (fun y : Nat × Nat => y.1) ha
  have hb' : p = b.1 := congrArg (fun y : Nat × Nat => y.1) hb
  exact h (ha'.symm.trans hb')

/-- In ONE common parent the actual row/column fibre contains infinitely
many real clones. No global Cartesian compatibility hypothesis is used. -/
theorem compatible_fibre_infinite (p r c : Nat) :
    (fibre (p,r) (p,c)).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : Nat => ((((p,r),c),n) : Real))
  · intro n m h
    exact congrArg Prod.snd h
  · intro n
    exact ⟨rfl,rfl⟩

end Hierarchical

/-- C29: there are literally no empty-base term generators in a unary
signature without constants; this statement names no chosen quotient point. -/
theorem actual_empty_term_closure {L : Language} {V : Type*}
    (H : Structure L V) : H.closure ∅ = ∅ := H.closure_empty

/-- C30: any finite clone window has only finite stabilizer orbits.
Thus these diagnostics cannot themselves certify the infinite HO equation. -/
theorem finite_window_orbits {V G : Type*} [Finite V] [Group G] [MulAction G V]
    (A : Set V) (u : V) :
    (orbitOver G A u).Finite ∧ ¬ (orbitOver G A u).Infinite := by
  have h : (orbitOver G A u).Finite := Set.toFinite _
  exact ⟨h,h.not_infinite⟩

end CCO.HereditaryHiddenOrbits.Boundaries
