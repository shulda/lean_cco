import CCO.HiddenSAPReadings.SourceSupport
import CCO.UnaryTermsReturn.CommonBlockSourceCertificate
import CCO.UnaryTermsReturn.CommonBlockMalformedObstruction
import CCO.UnaryFreshFrames.ClosureActions
import CCO.UnaryFreshFrames.Age
import CCO.GroupActions
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Source13: sharp language and support boundaries

The quotient diagonal below has distinct OLD real representatives. The
missing-transport example retains both actual old real sorts and their
proper quotient sorts; its matched pair relation is one full orbital.
Only the unary transport is omitted, and the corresponding orphan partner
is fixed by every full named automorphism but is outside unary closure.
Finite controls remain diagnostics, with no infinite theorem inferred
from a finite window. Higher arity requires its separate tuple/factor gate.
-/

namespace CCO.HiddenSAPReadings.Boundaries
open CCO.UnaryTermsReturn CCO.UnaryFreshFrames

namespace CommonBlock

/-- The actual original block quotient is identified with its block
label; this is a quotient equivalence, not a choice of real section. -/
def blockQuotientEquiv (i : Bool) :
    Quotient (commonBlockOldSetoid i) ≃ ℕ where
  toFun q := Quotient.liftOn q Prod.fst (by intro x y h; exact h)
  invFun q := Quotient.mk _ (q,0)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ x => exact Quotient.sound rfl
  right_inv _ := rfl

theorem actual_mixed_graph_pullback (x : CommonBlockReal false)
    (y : CommonBlockReal true) :
    commonBlockForward (Quotient.mk _ x) = Quotient.mk _ y ↔
      commonBlockOriginalAtomicSource.atomRel (i := false) (j := true) true x y := by
  change Quotient.mk (commonBlockOldSetoid false) x = Quotient.mk _ y ↔
    commonBlockOldColour false true x y = some true
  rw [Quotient.eq]
  change x.1 = y.1 ↔ commonBlockOldColour false true x y = some true
  simp [commonBlockOldColour]

/-- C62: the hidden quotient diagonal pulls back to genuine same-block
OLD DIVERSITY, while true old real equality never has diversity. -/
theorem quotient_diagonal_diversity (i : Bool) (x y : CommonBlockReal i)
    (hne : x ≠ y) :
    (Quotient.mk (commonBlockOldSetoid i) x = Quotient.mk _ y ↔
      commonBlockOriginalAtomicSource.atomRel true x y) := by
  change Quotient.mk (commonBlockOldSetoid i) x = Quotient.mk _ y ↔
    commonBlockOldColour i i x y = some true
  rw [Quotient.eq]
  have htag : (⟨i,x⟩ : Sigma CommonBlockReal) ≠ ⟨i,y⟩ := by
    intro h
    exact hne (sigma_mk_injective h)
  change x.1 = y.1 ↔ commonBlockOldColour i i x y = some true
  simp [commonBlockOldColour,htag]

theorem quotient_diagonal_has_distinct_old_representatives (i : Bool) (q : ℕ) :
    ∃ x y : CommonBlockReal i, x ≠ y ∧
      Quotient.mk (commonBlockOldSetoid i) x = Quotient.mk _ y := by
  exact ⟨(q,0),(q,1),by simp,Quotient.sound rfl⟩

theorem true_real_diagonal_empty_diversity (i : Bool) :
    ¬ ∃ x y : CommonBlockReal i, x ≠ y ∧ x = y := by
  rintro ⟨x,y,hne,he⟩
  exact hne he

/-- Both original visible hypotheses hold in this very infinite source. -/
theorem original_sap_and_cco :
    CCO.AgeSAP commonBlockOriginalAtomicSource ∧
      CCO.SemanticCCO.{0,0,0,0} commonBlockOriginalAtomicSource :=
  commonBlockOriginalSAPandCCO

end CommonBlock

namespace OmittedTransport

/-- The two real sorts are precisely the accepted common-block old
carriers. The other summand contains their two proper quotient copies. -/
abbrev Point := (Bool × (ℕ × ℕ)) ⊕ (Bool × ℕ)
abbrev Sorts := Bool ⊕ Bool
def real (i : Bool) (q n : ℕ) : Point := .inl (i,(q,n))
def quotient (i : Bool) (q : ℕ) : Point := .inr (i,q)

def sort : Point → Sorts
  | .inl (i,_) => .inl i
  | .inr (i,_) => .inr i

def root : Point → ℕ
  | .inl (_,q,_) => q
  | .inr (_,q) => q

/-- The hidden copies are the literal actual old quotient sets, merely
written through their proved block-label equivalences. -/
def actualQuotientNode (i : Bool) (q : Quotient (commonBlockOldSetoid i)) : Point :=
  quotient i (CommonBlock.blockQuotientEquiv i q)

abbrev language : Language where
  Sorts := Sorts
  Func := Bool
  Rel := Sorts × Sorts × Bool
  input F := .inl F
  output F := .inr F
  arity _ := 2
  argument R k := if k = 0 then R.1 else R.2.1

def operation (F : Bool) : Point → Point
  | .inl (i,(q,n)) => if i = F then quotient i q else real i q n
  | .inr x => .inr x

theorem projection_is_actual_old_quotient (i : Bool) (x : CommonBlockReal i) :
    operation i (real i x.1 x.2) =
      actualQuotientNode i (Quotient.mk (commonBlockOldSetoid i) x) := by
  change (if i = i then quotient i x.1 else real i x.1 x.2) = quotient i x.1
  simp

theorem omitted_match_is_actual_old_transition (q : Quotient (commonBlockOldSetoid false)) :
    actualQuotientNode true (commonBlockForward q) =
      quotient true (CommonBlock.blockQuotientEquiv false q) := rfl

/-- All distinct pair types of the common-block interpretation are
retained. Equal output points are handled by logical equality. -/
def model : Structure language Point where
  sort := sort
  func := operation
  func_sort := by
    intro F x hx
    rcases x with ⟨i,⟨q,n⟩⟩ | ⟨i,q⟩
    · have hi : i = F := Sum.inl.inj hx
      subst F
      simp [operation,sort,quotient]
    · cases hx
  func_offsort := by
    intro F x hx
    rcases x with ⟨i,⟨q,n⟩⟩ | ⟨i,q⟩
    · have hi : i ≠ F := fun h => hx (congrArg Sum.inl h)
      simp [operation,hi,real]
    · rfl
  rel R xs := sort (xs 0) = R.1 ∧ sort (xs 1) = R.2.1 ∧
    (if R.2.2 then root (xs 0) = root (xs 1) else root (xs 0) ≠ root (xs 1)) ∧
    xs 0 ≠ xs 1
  rel_sort R xs hx k := by
    fin_cases k
    · exact hx.1
    · exact hx.2.1

theorem quotient_ext {x : Point} {i : Bool} {q : ℕ}
    (hs : sort x = .inr i) (hr : root x = q) : x = quotient i q := by
  rcases x with ⟨j,⟨r,n⟩⟩ | ⟨j,r⟩
  · cases hs
  · have hj : j = i := Sum.inr.inj hs
    subst j
    exact congrArg (quotient i) hr

def pointEquiv (ρ : Equiv.Perm ℕ) : Equiv.Perm Point :=
  Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl Bool) (Equiv.prodCongr ρ (Equiv.refl ℕ)))
    (Equiv.prodCongr (Equiv.refl Bool) ρ)

theorem pointEquiv_sort (ρ : Equiv.Perm ℕ) (x : Point) :
    sort (pointEquiv ρ x) = sort x := by cases x <;> rfl

theorem pointEquiv_root (ρ : Equiv.Perm ℕ) (x : Point) :
    root (pointEquiv ρ x) = ρ (root x) := by cases x <;> rfl

/-- An actual original block permutation induces a full automorphism
of the language with both transport directions omitted. -/
def blockAut (ρ : Equiv.Perm ℕ) : model.Aut := by
  refine ⟨pointEquiv ρ,pointEquiv_sort ρ,?_,?_⟩
  · intro F x
    cases F <;> rcases x with ⟨i,⟨q,n⟩⟩ | ⟨i,q⟩ <;>
      cases i <;> rfl
  · intro R xs
    change (sort (pointEquiv ρ (xs 0)) = R.1 ∧
      sort (pointEquiv ρ (xs 1)) = R.2.1 ∧
      (if R.2.2 then root (pointEquiv ρ (xs 0)) = root (pointEquiv ρ (xs 1))
        else root (pointEquiv ρ (xs 0)) ≠ root (pointEquiv ρ (xs 1))) ∧
      pointEquiv ρ (xs 0) ≠ pointEquiv ρ (xs 1)) ↔ _
    rw [pointEquiv_sort,pointEquiv_sort,pointEquiv_root,pointEquiv_root]
    have hne : pointEquiv ρ (xs 0) ≠ pointEquiv ρ (xs 1) ↔ xs 0 ≠ xs 1 :=
      (pointEquiv ρ).injective.ne_iff
    cases hflag : R.2.2 <;> simp [model,hflag,ρ.injective.eq_iff,hne]

theorem match_relation (q : ℕ) :
    model.rel (.inr false,.inr true,true)
      ![quotient false q,quotient true q] := by
  refine ⟨rfl,rfl,rfl,?_⟩
  simp [quotient]

/-- The retained match predicate is ONE full actual pair orbital. -/
theorem matched_graph_is_one_full_orbital (q r : ℕ) :
    CCO.GroupActions.orbital (G := model.Aut)
      (quotient false 0) (quotient true 0)
      (quotient false q) (quotient true r) ↔ q = r := by
  constructor
  · rintro ⟨g,hgq,hgr⟩
    have h := (model.aut_rel g (.inr false,.inr true,true)
      ![quotient false 0,quotient true 0]).mpr (match_relation 0)
    change sort (g • quotient false 0) = .inr false ∧
      sort (g • quotient true 0) = .inr true ∧
      root (g • quotient false 0) = root (g • quotient true 0) ∧ _ at h
    have hroot := h.2.2.1
    change g.val (quotient false 0) = quotient false q at hgq
    change g.val (quotient true 0) = quotient true r at hgr
    change root (g.val (quotient false 0)) = root (g.val (quotient true 0)) at hroot
    rw [hgq,hgr] at hroot
    exact hroot
  · intro h
    subst r
    refine ⟨blockAut (Equiv.swap 0 q),?_,?_⟩
    · change quotient false (Equiv.swap 0 q 0) = quotient false q
      simp
    · change quotient true (Equiv.swap 0 q 0) = quotient true q
      simp

theorem partner_fixed (q : ℕ) (g : model.Aut)
    (hg : g • quotient false q = quotient false q) :
    g • quotient true q = quotient true q := by
  have hsort := model.aut_sort g (quotient true q)
  change sort (g • quotient true q) = Sum.inr true at hsort
  apply quotient_ext hsort
  have h := (model.aut_rel g (.inr false,.inr true,true)
    ![quotient false q,quotient true q]).mpr (match_relation q)
  change sort (g • quotient false q) = .inr false ∧
    sort (g • quotient true q) = .inr true ∧
    root (g • quotient false q) = root (g • quotient true q) ∧ _ at h
  rw [hg] at h
  exact h.2.2.1.symm

theorem orphan_closure (i : Bool) (q : ℕ) :
    model.closureAt (quotient i q) = {quotient i q} := by
  apply model.closure_eq
  intro F x hx
  have he : x = quotient i q := hx
  subst x
  rfl

/-- C63: algebraicity is in the FULL hidden group, while every named
unary term at the orphan is identity. Both old real sorts remain present. -/
theorem omitted_transport_orphan_algebraicity (q : ℕ) :
    quotient true q ∈ Dcl model.Aut {quotient false q} ∧
    quotient true q ∈ Acl model.Aut {quotient false q} ∧
    quotient true q ∉ model.closureAt (quotient false q) := by
  have hd : quotient true q ∈ Dcl model.Aut {quotient false q} := by
    intro g
    exact partner_fixed q g.val (g.property _ rfl)
  refine ⟨hd,dcl_subset_acl model.Aut _ hd,?_⟩
  rw [orphan_closure]
  simp [quotient]

end OmittedTransport

namespace EquivalenceInterpretation

/-- The ONE-old-sort infinite equivalence interpretation used by D10.
The proper quotient is the actual same-block quotient, written through
CommonBlock.blockQuotientEquiv. There is no other quotient copy whose
transport could be omitted. The hidden identity map is named explicitly. -/
abbrev Point := (ℕ × ℕ) ⊕ ℕ
def real (q n : ℕ) : Point := .inl (q,n)
def quotient (q : ℕ) : Point := .inr q
def sort : Point → Bool
  | .inl _ => false
  | .inr _ => true
def root : Point → ℕ
  | .inl (q,_) => q
  | .inr q => q

abbrev language : Language where
  Sorts := Bool
  Func := Bool
  Rel := Bool × Bool × Bool
  input F := F
  output _ := true
  arity _ := 2
  argument R k := if k = 0 then R.1 else R.2.1

def operation (F : Bool) : Point → Point
  | .inl (q,n) => if F then real q n else quotient q
  | .inr q => quotient q

/-- Every real/quotient pair carries its complete same-block or
different-block type; literal equality remains separate. -/
def model : Structure language Point where
  sort := sort
  func := operation
  func_sort := by
    rintro F (⟨q,n⟩ | q) hx <;> cases F <;>
      simp_all [language,sort,operation,real,quotient]
  func_offsort := by
    rintro F (⟨q,n⟩ | q) hx <;> cases F <;>
      simp_all [language,sort,operation,real,quotient]
  rel R xs := sort (xs 0) = R.1 ∧ sort (xs 1) = R.2.1 ∧
    (if R.2.2 then root (xs 0) = root (xs 1) else root (xs 0) ≠ root (xs 1)) ∧
    xs 0 ≠ xs 1
  rel_sort R xs h k := by
    fin_cases k
    · exact h.1
    · exact h.2.1

theorem projection_is_actual_quotient (x : CommonBlockReal false) :
    operation false (real x.1 x.2) =
      quotient (CommonBlock.blockQuotientEquiv false
        (Quotient.mk (commonBlockOldSetoid false) x)) := rfl

end EquivalenceInterpretation

namespace ReducibleAncestors
open CCO.UnarySupport
open CCO.UnarySupport.Structure
open EquivalenceInterpretation

/-- x,y,u,v respectively. Both reals belong to ONE old real sort and
u,v are their actual same-block quotient values. -/
def point : Fin 4 → EquivalenceInterpretation.Point
  | 0 => real 0 0
  | 1 => real 1 0
  | 2 => quotient 0
  | _ => quotient 1

theorem point_injective : Function.Injective point := by decide

def allowed (x y : Fin 4) : Prop :=
  (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) ∨
  (x = 1 ∧ y = 3) ∨ (x = 3 ∧ y = 1) ∨
  (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2)

/-- The partial diagram contains the two full one-generated diagrams
and the off-diagonal quotient pair; ancestor cross tuples are absent. -/
def source : CCO.UnarySupport.Structure (partialSignature language) (Fin 4) where
  sort x := (partialTarget model).sort (point x)
  func F x := {y | point y ∈ (partialTarget model).func F (point x)}
  functional F x y z hy hz := point_injective
    ((partialTarget model).functional F (point x) (point y) (point z) hy hz)
  func_sorted F x y hy := (partialTarget model).func_sorted F (point x) (point y) hy
  rel R xs := by
    change Fin 2 → Fin 4 at xs
    exact (partialTarget model).rel R (point ∘ xs) ∧ allowed (xs 0) (xs 1)
  rel_sorted R xs h := by
    change Fin 2 → Fin 4 at xs
    change (partialTarget model).rel R (point ∘ xs) ∧ allowed (xs 0) (xs 1) at h
    exact (partialTarget model).rel_sorted R (point ∘ xs) h.1

theorem source_func_iff (F : Bool) (x y : Fin 4) :
    y ∈ source.func F x ↔
      (F = false ∧ ((x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 3))) ∨
      (F = true ∧ x = y ∧ (x = 2 ∨ x = 3)) := by
  fin_cases x <;> fin_cases y <;> cases F <;>
    simp [source,point,partialTarget,model,operation,EquivalenceInterpretation.sort,language,real,quotient]

theorem quotient_pair_is_displayed : source.rel (true,true,false) ![2,3] := by
  refine ⟨?_,?_⟩
  · exact ⟨rfl,rfl,by decide,by decide⟩
  · simp [allowed]

theorem no_real_ancestor_relation (R : (partialSignature language).Rel) :
    ¬ source.rel R ![0,1] := by
  intro h
  have ha : allowed (0 : Fin 4) 1 := h.2
  simp [allowed] at ha

theorem closed_iff (D : Set (Fin 4)) :
    source.IsClosed D ↔ (0 ∈ D → 2 ∈ D) ∧ (1 ∈ D → 3 ∈ D) := by
  constructor
  · intro h
    exact ⟨fun h0 => h false 0 h0 ((source_func_iff false 0 2).mpr (by simp)),
      fun h1 => h false 1 h1 ((source_func_iff false 1 3).mpr (by simp))⟩
  · rintro ⟨h0,h1⟩ F x hx y hy
    rcases (source_func_iff F x y).mp hy with ⟨rfl,hxy⟩ | ⟨rfl,hxy,_⟩
    · rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact h0 hx
      · exact h1 hx
    · exact hxy ▸ hx

def left : Set (Fin 4) := {x | x ≠ 1}
def right : Set (Fin 4) := {x | x ≠ 0}

/-- C61: the actual unary-closed factors are {x,u,v} and {y,u,v}.
Every displayed tuple lies in one factor, and the quotient tuple lies
in their common base. This is a genuine free decomposition. -/
def ancestorSplit : source.FreeDecomposition where
  left := left
  right := right
  left_closed := (closed_iff left).mpr ⟨by simp [left],by simp [left]⟩
  right_closed := (closed_iff right).mpr ⟨by simp [right],by simp [right]⟩
  cover := by ext x; fin_cases x <;> simp [left,right]
  left_proper := by
    intro h
    have h1 : (1 : Fin 4) ∈ left := by rw [h]; trivial
    exact h1 rfl
  right_proper := by
    intro h
    have h0 : (0 : Fin 4) ∈ right := by rw [h]; trivial
    exact h0 rfl
  rel_local R xs h := by
    change Fin 2 → Fin 4 at xs
    have hpair : (xs 0 ∈ left ∧ xs 1 ∈ left) ∨
        (xs 0 ∈ right ∧ xs 1 ∈ right) := by
      rcases h.2 with h | h | h | h | h | h <;>
        rcases h with ⟨h0,h1⟩ <;> simp [h0,h1,left,right]
    rcases hpair with hl | hr
    · exact Or.inl (by intro i; fin_cases i; exact hl.1; exact hl.2)
    · exact Or.inr (by intro i; fin_cases i; exact hr.1; exact hr.2)

theorem intersection_is_quotient_base :
    left ∩ right = ({2,3} : Set (Fin 4)) := by
  ext x
  fin_cases x <;> simp [left,right]

theorem two_root_closure_full : source.closure ({0,1} : Set (Fin 4)) = Set.univ := by
  have h0 := source.subset_closure ({0,1} : Set (Fin 4)) (by simp : (0 : Fin 4) ∈ ({0,1} : Set (Fin 4)))
  have h1 := source.subset_closure ({0,1} : Set (Fin 4)) (by simp : (1 : Fin 4) ∈ ({0,1} : Set (Fin 4)))
  have hclosed := (closed_iff (source.closure ({0,1} : Set (Fin 4)))).mp
    (source.isClosed_closure _)
  apply Set.eq_univ_of_forall
  intro x
  fin_cases x
  · exact h0
  · exact h1
  · exact hclosed.1 h0
  · exact hclosed.2 h1

theorem related_descendants_do_not_make_ancestors_irreducible :
    ¬ source.Irreducible := fun h => h.false ancestorSplit

def root0Split : source.FreeDecomposition where
  left := {x | x ≠ 0}
  right := {x | x = 0 ∨ x = 2}
  left_closed := (closed_iff _).mpr ⟨by simp,by simp⟩
  right_closed := (closed_iff _).mpr ⟨by simp,by simp⟩
  cover := by ext x; fin_cases x <;> simp
  left_proper := by
    intro h
    have h0 : (0 : Fin 4) ∈ ({x | x ≠ 0} : Set (Fin 4)) := by rw [h]; trivial
    exact h0 rfl
  right_proper := by
    intro h
    have h3 : (3 : Fin 4) ∈ ({x | x = 0 ∨ x = 2} : Set (Fin 4)) := by rw [h]; trivial
    simpa using h3
  rel_local R xs h := by
    change Fin 2 → Fin 4 at xs
    have hpair :
        (xs 0 ≠ 0 ∧ xs 1 ≠ 0) ∨
        ((xs 0 = 0 ∨ xs 0 = 2) ∧ (xs 1 = 0 ∨ xs 1 = 2)) := by
      rcases h.2 with h | h | h | h | h | h <;>
        rcases h with ⟨h0,h1⟩ <;> simp [h0,h1]
    rcases hpair with hl | hr
    · exact Or.inl (by intro i; fin_cases i; exact hl.1; exact hl.2)
    · exact Or.inr (by intro i; fin_cases i; exact hr.1; exact hr.2)

def root1Split : source.FreeDecomposition where
  left := {x | x ≠ 1}
  right := {x | x = 1 ∨ x = 3}
  left_closed := (closed_iff _).mpr ⟨by simp,by simp⟩
  right_closed := (closed_iff _).mpr ⟨by simp,by simp⟩
  cover := by ext x; fin_cases x <;> simp
  left_proper := by
    intro h
    have h1 : (1 : Fin 4) ∈ ({x | x ≠ 1} : Set (Fin 4)) := by rw [h]; trivial
    exact h1 rfl
  right_proper := by
    intro h
    have h2 : (2 : Fin 4) ∈ ({x | x = 1 ∨ x = 3} : Set (Fin 4)) := by rw [h]; trivial
    simpa using h2
  rel_local R xs h := by
    change Fin 2 → Fin 4 at xs
    have hpair :
        (xs 0 ≠ 1 ∧ xs 1 ≠ 1) ∨
        ((xs 0 = 1 ∨ xs 0 = 3) ∧ (xs 1 = 1 ∨ xs 1 = 3)) := by
      rcases h.2 with h | h | h | h | h | h <;>
        rcases h with ⟨h0,h1⟩ <;> simp [h0,h1]
    rcases hpair with hl | hr
    · exact Or.inl (by intro i; fin_cases i; exact hl.1; exact hl.2)
    · exact Or.inr (by intro i; fin_cases i; exact hr.1; exact hr.2)

def restrictSplit (d : source.FreeDecomposition) (D : Set (Fin 4))
    (hD : source.IsClosed D) {x y : Fin 4}
    (hx : x ∈ D) (hy : y ∈ D) (hxl : x ∉ d.left) (hyr : y ∉ d.right) :
    (source.induce D hD).FreeDecomposition where
  left := {z | z.val ∈ d.left}
  right := {z | z.val ∈ d.right}
  left_closed F z hz t ht := d.left_closed F z.val hz ht
  right_closed F z hz t ht := d.right_closed F z.val hz ht
  cover := by
    apply Set.eq_univ_of_forall
    intro z
    have h : z.val ∈ d.left ∪ d.right := by rw [d.cover]; trivial
    exact h
  left_proper := by
    intro h
    have hmem : (⟨x,hx⟩ : D) ∈ {z | z.val ∈ d.left} := h ▸ Set.mem_univ _
    exact hxl hmem
  right_proper := by
    intro h
    have hmem : (⟨y,hy⟩ : D) ∈ {z | z.val ∈ d.right} := h ▸ Set.mem_univ _
    exact hyr hmem
  rel_local R xs hr := d.rel_local R (Subtype.val ∘ xs) hr

theorem irreducible_avoids_missing_pairs (D : Set (Fin 4))
    (hD : source.IsClosed D) (hirr : (source.induce D hD).Irreducible) :
    (¬ (0 ∈ D ∧ 1 ∈ D)) ∧ (¬ (0 ∈ D ∧ 3 ∈ D)) ∧
      (¬ (1 ∈ D ∧ 2 ∈ D)) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨h0,h1⟩
    exact hirr.false (restrictSplit ancestorSplit D hD h1 h0 (by simp [ancestorSplit,left]) (by simp [ancestorSplit,right]))
  · rintro ⟨h0,h3⟩
    exact hirr.false (restrictSplit root0Split D hD h0 h3 (by simp [root0Split]) (by simp [root0Split]))
  · rintro ⟨h1,h2⟩
    exact hirr.false (restrictSplit root1Split D hD h1 h2 (by simp [root1Split]) (by simp [root1Split]))

theorem allowed_of_irreducible (D : Set (Fin 4))
    (hD : source.IsClosed D) (hirr : (source.induce D hD).Irreducible)
    {x y : Fin 4} (hx : x ∈ D) (hy : y ∈ D) (hne : x ≠ y) : allowed x y := by
  have hno := irreducible_avoids_missing_pairs D hD hirr
  fin_cases x <;> fin_cases y <;> simp_all [allowed]

def completion : Hom source (partialTarget model) where
  point := point
  sort_eq _ := rfl
  map_func _ _ _ h := h
  map_rel _ _ h := h.1

theorem reflect_target_function (F : Bool) (x : Fin 4)
    (y : EquivalenceInterpretation.Point)
    (hy : y ∈ (partialTarget model).func F (point x)) :
    ∃ z : Fin 4, z ∈ source.func F x ∧ point z = y := by
  fin_cases x <;> cases F <;>
    simp [partialTarget,model,EquivalenceInterpretation.sort,operation,point,real,quotient,language] at hy
  · subst y
    exact ⟨2,(source_func_iff false 0 2).mpr (by simp),rfl⟩
  · subst y
    exact ⟨3,(source_func_iff false 1 3).mpr (by simp),rfl⟩
  · subst y
    exact ⟨2,(source_func_iff true 2 2).mpr (by simp),rfl⟩
  · subst y
    exact ⟨3,(source_func_iff true 3 3).mpr (by simp),rfl⟩

/-- The reducible partial diagram really has an HE completion in an
infinite actual equivalence interpretation. No ancestor colour is filled
in the source: reflection is required exactly on its irreducible pieces. -/
theorem completion_is_HE : completion.HomEmbedding := by
  intro D hD hirr
  refine ⟨point_injective.injOn,?_,?_⟩
  · intro R xs hxs
    change Fin 2 → Fin 4 at xs
    constructor
    · intro h
      refine ⟨h,allowed_of_irreducible D hD hirr
        (hxs (0 : Fin 2)) (hxs (1 : Fin 2)) ?_⟩
      intro he
      exact h.2.2.2 (congrArg point he)
    · exact completion.map_rel R xs
  · intro F x hx y hy
    obtain ⟨z,hz,hzy⟩ := reflect_target_function F x y hy
    exact ⟨z,hD F x hx hz,hz,hzy⟩

theorem completion_image_closed :
    (partialTarget model).IsClosed (Set.range point) := by
  rintro F _ ⟨x,rfl⟩ y hy
  obtain ⟨z,_,hz⟩ := reflect_target_function F x y hy
  exact ⟨z,hz⟩

/-- The completion target is an ACTUAL finite closed induced member
of the one-sort equivalence interpretation, rather than the infinite
ambient structure or an asserted arbitrary completion provider. -/
def completedTargetPiece : model.Piece :=
  ⟨Set.range point,Set.finite_range _,
    (partialTarget_closed_iff model _).mp completion_image_closed⟩

def completionIntoPiece : Hom source
    ((partialTarget model).induce (Set.range point) completion_image_closed) where
  point x := ⟨point x,⟨x,rfl⟩⟩
  sort_eq _ := rfl
  map_func _ _ _ h := h
  map_rel _ _ h := h.1

theorem completion_into_finite_piece_is_HE : completionIntoPiece.HomEmbedding := by
  intro D hD hirr
  have hOld := completion_is_HE D hD hirr
  refine ⟨?_,hOld.2.1,?_⟩
  · intro x hx y hy hxy
    exact hOld.1 hx hy (congrArg Subtype.val hxy)
  · intro F x hx y hy
    obtain ⟨z,hzD,hz,hzy⟩ := hOld.2.2 F x hx y.val hy
    exact ⟨z,hzD,hz,Subtype.ext hzy⟩

theorem reducible_but_HE_completable :
    source.closure ({0,1} : Set (Fin 4)) = Set.univ ∧
    ¬ source.Irreducible ∧ completionIntoPiece.HomEmbedding :=
  ⟨two_root_closure_full,related_descendants_do_not_make_ancestors_irreducible,
    completion_into_finite_piece_is_HE⟩

end ReducibleAncestors

/-- C64: the union of two actual complete orbitals need not itself be
an orbital. Equality is invariant under every permutation, so a single
orbit cannot contain both the diagonal and a distinct pair. -/
theorem union_of_two_orbitals_not_one :
    ¬ ∃ a b : ℕ, CCO.GroupActions.orbital (G := Equiv.Perm ℕ) a b =
      (fun x y => CCO.GroupActions.orbital (G := Equiv.Perm ℕ) 0 0 x y ∨
        CCO.GroupActions.orbital (G := Equiv.Perm ℕ) 0 1 x y) := by
  rintro ⟨a,b,h⟩
  have h00 : CCO.GroupActions.orbital (G := Equiv.Perm ℕ) a b 0 0 := by
    rw [h]
    exact Or.inl (CCO.GroupActions.orbital_nonempty 0 0)
  have h01 : CCO.GroupActions.orbital (G := Equiv.Perm ℕ) a b 0 1 := by
    rw [h]
    exact Or.inr (CCO.GroupActions.orbital_nonempty 0 1)
  obtain ⟨g,hga,hgb⟩ := h00
  have hab : a = b := (MulAction.injective g) (hga.trans hgb.symm)
  obtain ⟨k,hka,hkb⟩ := h01
  have hbad : (0 : ℕ) = 1 := hka.symm.trans ((congrArg (fun x => k • x) hab).trans hkb)
  exact Nat.zero_ne_one hbad

/-- C66: the accepted actual old SAP+CCO source also has malformed
partial unary cycles with no uniform small closed obstruction window.
Thus the chosen singleton bound in SourceSupport cannot be dropped. -/
theorem arbitrary_partial_sources_have_no_uniform_bound (N : ℕ) :
    CCO.AgeSAP commonBlockOriginalAtomicSource ∧
    CCO.SemanticCCO.{0,0,0,0} commonBlockOriginalAtomicSource ∧
    ∃ n : ℕ, 2 ≤ n ∧ N < Fintype.card (Fin n ⊕ Fin n) ∧
      (∀ A B : Set (Fin n), MalformedCycleClosed A B →
        A.ncard + B.ncard ≤ N → A = ∅ ∧ B = ∅) ∧
      (∀ imageA : Fin n → Quotient (commonBlockOldSetoid false),
        ∀ imageB : Fin n → Quotient (commonBlockOldSetoid true),
          (∀ i, imageB i = commonBlockForward (imageA i)) →
          (∀ i, imageA (malformedCycleStep n i) = commonBlockBackward (imageB i)) →
          ¬ Function.Injective imageA) :=
  commonBlockMalformed_no_uniform_closed_obstruction N

end CCO.HiddenSAPReadings.Boundaries
