import CCO.ExactEPGeometry.MarkedTriples
import Mathlib.Tactic.FinCases

/-!
# B062 C21: exact marked pair homogeneity and the real diagonal

The literal old optional colour, including `none` for actual equality,
determines the complete two-point equality pattern. Old symmetry
determines the reversed colour, while the unary owner code determines
the diagonal. These facts are read from real finite charts in the
genuine marked limit, not presumed for an arbitrary coloured table.
Consequently the accepted marked-limit tuple homogeneity aligns ANY
two complete endpoint pairs with the same owner and forward colour.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open scoped FirstOrder

noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Equality on the original carrier is never a separate diversity edge.
If the actual old full pair code is the diagonal code, its two old
points must be equal (also for cross-sort or repeated presentations). -/
theorem tagged_colour_diagonal_eq (p q : Sigma X) (i : ι)
    (h : taggedColour S p q =
      (⟨i,i,none⟩ : APCharacter.Age.Colour S)) : p = q := by
  rcases p with ⟨j,a⟩
  rcases q with ⟨k,b⟩
  have hj : j = i := congrArg Sigma.fst h
  have hk : k = i := congrArg
    (fun z : APCharacter.Age.Colour S => z.2.1) h
  cases hj
  cases hk
  have hnone : S.colour a b = none := by
    simpa only [taggedColour, Sigma.mk.injEq, heq_eq_eq, true_and] using h
  exact (S.colour_none_iff a b).mp hnone

/-- Full original-pair coding is symmetrically determined: if two
old ordered pairs have the same actual optional colour and sort names,
then their reversed pairs also have the same full code. -/
theorem tagged_colour_reverse_eq
    (p q r s : Sigma X)
    (h : taggedColour S p q = taggedColour S r s) :
    taggedColour S q p = taggedColour S s r := by
  rcases p with ⟨i,a⟩
  rcases q with ⟨j,b⟩
  rcases r with ⟨k,c⟩
  rcases s with ⟨l,d⟩
  have hi : i = k := congrArg Sigma.fst h
  have hj : j = l := congrArg
    (fun z : APCharacter.Age.Colour S => z.2.1) h
  cases hi
  cases hj
  have hColour : S.colour a b = S.colour c d := by
    simpa only [taggedColour, Sigma.mk.injEq, heq_eq_eq, true_and] using h
  have hrev : S.colour b a = S.colour d c := by
    calc
      _ = (S.colour a b).map (fun t => S.conv t) := S.colour_reverse a b
      _ = (S.colour c d).map (fun t => S.conv t) := by rw [hColour]
      _ = S.colour d c := (S.colour_reverse c d).symm
  exact congrArg (fun z : Option (S.Atom j i) =>
    (⟨j,i,z⟩ : APCharacter.Age.Colour S)) hrev

variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) {M : APCharacter.MaskData S}
variable (completion : APCharacter.Age.CompletionProperty S M)

/-- Read both orders of a marked pair from one ACTUAL finite chart of the
same homogeneous marked limit. Its two old endpoints may be equal. -/
theorem marked_pair_chart_codes
    (a b : APCharacter.Age.Limit S H completion) :
    ∃ p q : Sigma X,
      (APCharacter.Age.limitCoding S H completion).table.colour a b =
        APCharacter.Age.colourEquiv S (taggedColour S p q) ∧
      (APCharacter.Age.limitCoding S H completion).table.colour b a =
        APCharacter.Age.colourEquiv S (taggedColour S q p) := by
  let pair : Fin 2 → APCharacter.Age.Limit S H completion := ![a,b]
  obtain ⟨C, q, _, hc⟩ :=
    APCharacter.Age.finite_tuple_names S H completion pair
  refine ⟨C.point (q 0), C.point (q 1), ?_, ?_⟩
  · calc
      (APCharacter.Age.limitCoding S H completion).table.colour a b =
          (APCharacter.Age.limitCoding S H completion).table.colour (pair 0) (pair 1) := by
            simp [pair]
      _ = C.table.colour (q 0) (q 1) := hc 0 1
      _ = APCharacter.Age.colourEquiv S (taggedColour S (C.point (q 0)) (C.point (q 1))) :=
        congrArg (fun T : APCharacter.Age.Table S (Fin C.size) => T.colour (q 0) (q 1))
          C.table_eq
  · calc
      (APCharacter.Age.limitCoding S H completion).table.colour b a =
          (APCharacter.Age.limitCoding S H completion).table.colour (pair 1) (pair 0) := by
            simp [pair]
      _ = C.table.colour (q 1) (q 0) := hc 1 0
      _ = APCharacter.Age.colourEquiv S (taggedColour S (C.point (q 1)) (C.point (q 0))) :=
        congrArg (fun T : APCharacter.Age.Table S (Fin C.size) => T.colour (q 1) (q 0))
          C.table_eq

/-- Equal forward marked pair colours imply equal REVERSED marked pair
colours. This is proved via the genuine source's reversal, not imposed as
a new axiom on the finite colouring table. -/
theorem marked_reverse_code_eq
    (a b c d : APCharacter.Age.Limit S H completion)
    (h : (APCharacter.Age.limitCoding S H completion).table.colour a b =
      (APCharacter.Age.limitCoding S H completion).table.colour c d) :
    (APCharacter.Age.limitCoding S H completion).table.colour b a =
      (APCharacter.Age.limitCoding S H completion).table.colour d c := by
  obtain ⟨p,q,hPQ,hQP⟩ := marked_pair_chart_codes S H completion a b
  obtain ⟨r,s,hRS,hSR⟩ := marked_pair_chart_codes S H completion c d
  have same : taggedColour S p q = taggedColour S r s :=
    (APCharacter.Age.colourEquiv S).injective (hPQ.symm.trans (h.trans hRS))
  calc
    (APCharacter.Age.limitCoding S H completion).table.colour b a =
        APCharacter.Age.colourEquiv S (taggedColour S q p) := hQP
    _ = APCharacter.Age.colourEquiv S (taggedColour S s r) :=
      congrArg (APCharacter.Age.colourEquiv S) (tagged_colour_reverse_eq S p q r s same)
    _ = (APCharacter.Age.limitCoding S H completion).table.colour d c := hSR.symm

/-- The actual diagonal colour is fixed by the original named sort.
The complete owner code is read from a real singleton finite chart;
no arbitrary extra equality-coloured diversity pairs are supplied. -/
theorem marked_diagonal_of_owner
    (a : APCharacter.Age.Limit S H completion)
    (i : ι) (ε : Bit)
    (hOwner : (APCharacter.Age.limitCoding S H completion).table.owner a =
      APCharacter.Age.ownerEquiv S (i,ε)) :
    (APCharacter.Age.limitCoding S H completion).table.colour a a =
      APCharacter.Age.colourEquiv S (⟨i,i,none⟩ : APCharacter.Age.Colour S) := by
  let one : Fin 1 → APCharacter.Age.Limit S H completion := fun _ => a
  obtain ⟨C,q,ho,hc⟩ := APCharacter.Age.finite_tuple_names S H completion one
  have hOriginal : APCharacter.Age.ownerEquiv S
      ((C.point (q 0)).1, C.bits (q 0)) =
      APCharacter.Age.ownerEquiv S (i,ε) := by
    calc
      _ = C.table.owner (q 0) :=
        (congrArg (fun T : APCharacter.Age.Table S (Fin C.size) => T.owner (q 0))
          C.table_eq).symm
      _ = (APCharacter.Age.limitCoding S H completion).table.owner a := (ho 0).symm
      _ = APCharacter.Age.ownerEquiv S (i,ε) := hOwner
  have hsort : (C.point (q 0)).1 = i :=
    congrArg Prod.fst ((APCharacter.Age.ownerEquiv S).injective hOriginal)
  have hName :
      (APCharacter.Age.limitCoding S H completion).table.colour a a =
      APCharacter.Age.colourEquiv S
        (taggedColour S (C.point (q 0)) (C.point (q 0))) := by
    calc
      _ = C.table.colour (q 0) (q 0) := hc 0 0
      _ = APCharacter.Age.colourEquiv S
        (taggedColour S (C.point (q 0)) (C.point (q 0))) :=
          congrArg (fun T : APCharacter.Age.Table S (Fin C.size) =>
            T.colour (q 0) (q 0)) C.table_eq
  rcases hpoint : C.point (q 0) with ⟨j,x⟩
  have hj : j = i := by simpa [hpoint] using hsort
  have hnone : S.colour x x = none := (S.colour_none_iff x x).mpr rfl
  have hTag : taggedColour S (C.point (q 0)) (C.point (q 0)) =
      (⟨i,i,none⟩ : APCharacter.Age.Colour S) := by
    rw [hpoint]
    change (⟨j,j,S.colour x x⟩ : APCharacter.Age.Colour S) =
      (⟨i,i,none⟩ : APCharacter.Age.Colour S)
    rw [hj, hnone]
  exact hName.trans (congrArg (APCharacter.Age.colourEquiv S) hTag)

/-- A diagonal marked pair has some REAL original diagonal code, whose
sort is its owner sort. Useful for equality-pattern reflection. -/
theorem marked_diagonal_exists
    (a : APCharacter.Age.Limit S H completion) :
    ∃ i : ι, (APCharacter.Age.limitCoding S H completion).table.colour a a =
      APCharacter.Age.colourEquiv S (⟨i,i,none⟩ : APCharacter.Age.Colour S) := by
  let p : ι × Bit :=
    (APCharacter.Age.ownerEquiv S).symm
      ((APCharacter.Age.limitCoding S H completion).table.owner a)
  have hOwner :
      (APCharacter.Age.limitCoding S H completion).table.owner a =
        APCharacter.Age.ownerEquiv S p :=
    ((APCharacter.Age.ownerEquiv S).apply_symm_apply _).symm
  rcases p with ⟨i,ε⟩
  exact ⟨i, marked_diagonal_of_owner S H completion a i ε hOwner⟩

/-- The CURRENT marked limit cannot contain a nontrivial equality-coloured
pair. The proof extracts an actual injective OLD two-point witness from
the genuine finite age and uses the true original diagonal. -/
theorem marked_eq_of_diagonal_colour
    (a b : APCharacter.Age.Limit S H completion) (i : ι)
    (h : (APCharacter.Age.limitCoding S H completion).table.colour a b =
      APCharacter.Age.colourEquiv S (⟨i,i,none⟩ : APCharacter.Age.Colour S)) :
    a = b := by
  by_contra hneq
  let pair : Fin 2 → APCharacter.Age.Limit S H completion := ![a,b]
  have hinj : Function.Injective pair := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact False.elim (hneq (by simpa [pair] using hxy))
    · exact False.elim (hneq (by simpa [pair] using hxy.symm))
    · rfl
  obtain ⟨old,bits,oldInj,_,_,hcol⟩ :=
    APCharacter.Age.finite_old_witness S H completion pair hinj
  have hOldColour : taggedColour S (old 0) (old 1) =
      (⟨i,i,none⟩ : APCharacter.Age.Colour S) := by
    apply (APCharacter.Age.colourEquiv S).injective
    calc
      APCharacter.Age.colourEquiv S (taggedColour S (old 0) (old 1)) =
          (APCharacter.Age.limitCoding S H completion).table.colour (pair 0) (pair 1) :=
            (hcol 0 1).symm
      _ = (APCharacter.Age.limitCoding S H completion).table.colour a b := by
        simp [pair]
      _ = APCharacter.Age.colourEquiv S (⟨i,i,none⟩ : APCharacter.Age.Colour S) := h
  have oldEq : old 0 = old 1 :=
    tagged_colour_diagonal_eq S (old 0) (old 1) i hOldColour
  have impossible : (0 : Fin 2) ≠ 1 := by decide
  exact impossible (oldInj oldEq)

/-- Equality patterns of marked endpoint pairs depend ONLY on the
complete coded forward pair colour. The implication for different
points is proved rather than assumed in a relational table. -/
theorem marked_same_colour_eq_iff
    (a b c d : APCharacter.Age.Limit S H completion)
    (h : (APCharacter.Age.limitCoding S H completion).table.colour a b =
      (APCharacter.Age.limitCoding S H completion).table.colour c d) :
    (a = b ↔ c = d) := by
  constructor
  · intro he
    subst b
    obtain ⟨i,hi⟩ := marked_diagonal_exists S H completion a
    exact marked_eq_of_diagonal_colour S H completion c d i (h.symm.trans hi)
  · intro he
    subst d
    obtain ⟨i,hi⟩ := marked_diagonal_exists S H completion c
    exact marked_eq_of_diagonal_colour S H completion a b i (h.trans hi)

/-- Identical current owner codes entail the same actual diagonal
colour, even if two different vertices carry that owner. -/
theorem marked_same_owner_diagonal
    (a b : APCharacter.Age.Limit S H completion)
    (hOwner : (APCharacter.Age.limitCoding S H completion).table.owner a =
      (APCharacter.Age.limitCoding S H completion).table.owner b) :
    (APCharacter.Age.limitCoding S H completion).table.colour a a =
      (APCharacter.Age.limitCoding S H completion).table.colour b b := by
  let p : ι × Bit :=
    (APCharacter.Age.ownerEquiv S).symm
      ((APCharacter.Age.limitCoding S H completion).table.owner a)
  have ha : (APCharacter.Age.limitCoding S H completion).table.owner a =
      APCharacter.Age.ownerEquiv S p :=
    ((APCharacter.Age.ownerEquiv S).apply_symm_apply _).symm
  have hb : (APCharacter.Age.limitCoding S H completion).table.owner b =
      APCharacter.Age.ownerEquiv S p := hOwner.symm.trans ha
  rcases p with ⟨i,ε⟩
  exact (marked_diagonal_of_owner S H completion a i ε ha).trans
    (marked_diagonal_of_owner S H completion b i ε hb).symm

/-- Full C21 endpoint alignment: the SAME actual complete two-point
marked-language coding gives a global automorphism carrying BOTH source
endpoints to arbitrary target endpoints. Exact equality cases are preserved.
This is the real `Age.tuple_homogeneous` instance, not a pair-orbit axiom. -/
theorem marked_align_endpoints
    (a b c d : APCharacter.Age.Limit S H completion)
    (hOwnerA : (APCharacter.Age.limitCoding S H completion).table.owner a =
      (APCharacter.Age.limitCoding S H completion).table.owner c)
    (hOwnerB : (APCharacter.Age.limitCoding S H completion).table.owner b =
      (APCharacter.Age.limitCoding S H completion).table.owner d)
    (hColour : (APCharacter.Age.limitCoding S H completion).table.colour a b =
      (APCharacter.Age.limitCoding S H completion).table.colour c d) :
    ∃ g : APCharacter.Age.Limit S H completion ≃[APCharacter.Age.Language S]
      APCharacter.Age.Limit S H completion,
      g a = c ∧ g b = d := by
  let src : Bool → APCharacter.Age.Limit S H completion :=
    fun v => if v then b else a
  let tgt : Bool → APCharacter.Age.Limit S H completion :=
    fun v => if v then d else c
  have hEq : a = b ↔ c = d :=
    marked_same_colour_eq_iff S H completion a b c d hColour
  have hEqMap : ∀ i j, src i = src j ↔ tgt i = tgt j := by
    intro i j
    cases i <;> cases j
    · simp
    · simpa [src,tgt] using hEq
    · change (b = a ↔ d = c)
      constructor
      · intro e
        exact (hEq.mp e.symm).symm
      · intro e
        exact (hEq.mpr e.symm).symm
    · simp
  have hOwner : ∀ i,
      (APCharacter.Age.limitCoding S H completion).table.owner (src i) =
      (APCharacter.Age.limitCoding S H completion).table.owner (tgt i) := by
    intro i
    cases i
    · simpa [src,tgt] using hOwnerA
    · simpa [src,tgt] using hOwnerB
  have hColourMap : ∀ i j,
      (APCharacter.Age.limitCoding S H completion).table.colour (src i) (src j) =
      (APCharacter.Age.limitCoding S H completion).table.colour (tgt i) (tgt j) := by
    intro i j
    cases i <;> cases j
    · simpa [src,tgt] using marked_same_owner_diagonal S H completion a c hOwnerA
    · simpa [src,tgt] using hColour
    · simpa [src,tgt] using marked_reverse_code_eq S H completion a b c d hColour
    · simpa [src,tgt] using marked_same_owner_diagonal S H completion b d hOwnerB
  obtain ⟨g,hg⟩ :=
    APCharacter.Age.tuple_homogeneous S H completion src tgt hEqMap hOwner hColourMap
  refine ⟨g, ?_, ?_⟩
  · simpa [src,tgt] using hg false
  · simpa [src,tgt] using hg true

end
end CCO.ExactEPGeometry
