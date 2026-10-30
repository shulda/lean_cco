import CCO.FullPhaseLift.Canonical.Profiles
import CCO.Finite

/-! The actual typed pair reduct of the old full relational structure.
Finiteness comes from finite full atomic profiles. Same-sort symmetry is
the explicit binary-source assumption A02, and is not inferred from full
homogeneity. -/

universe v w
namespace CCO.FullPhaseLift.Canonical
attribute [local instance] Classical.propDecidable

abbrev UnaryName {L : Signature} {M : Type v} (T : BoolTable L M) :=
  {s : Profile L 1 // ∃ x, unaryProfile T x = s}

abbrev Carrier {L : Signature} {M : Type v} (T : BoolTable L M) (i : UnaryName T) :=
  {x : M // unaryProfile T x = i.val}

abbrev PairAtom {L : Signature} {M : Type v} (T : BoolTable L M) (i j : UnaryName T) :=
  {p : Profile L 2 // ∃ (x : Carrier T i) (y : Carrier T j),
    x.val ≠ y.val ∧ pairProfile T x.val y.val = p}

noncomputable instance {L : Signature} {M : Type v} (T : BoolTable L M) :
    Fintype (UnaryName T) := Fintype.ofFinite _

noncomputable instance {L : Signature} {M : Type v} (T : BoolTable L M)
    (i j : UnaryName T) : Fintype (PairAtom T i j) := Fintype.ofFinite _

instance {L : Signature} {M : Type v} (T : BoolTable L M) (i : UnaryName T) :
    Nonempty (Carrier T i) := by
  rcases i.property with ⟨x,h⟩
  exact ⟨⟨x,h⟩⟩

def pack {L : Signature} {M : Type v} (T : BoolTable L M) : M ≃ Sigma (Carrier T) where
  toFun x := ⟨⟨unaryProfile T x,⟨x,rfl⟩⟩,⟨x,rfl⟩⟩
  invFun p := p.2.val
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨i,hi⟩,⟨x,hx⟩⟩
    simp only [Carrier] at hx
    subst i
    rfl

@[simp] theorem pack_val {L : Signature} {M : Type v} (T : BoolTable L M) (x : M) :
    ((pack T x).2).val = x := rfl

def SameSortSymmetric {L : Signature} {M : Type v} (T : BoolTable L M) : Prop :=
  ∀ x y, unaryProfile T x = unaryProfile T y → pairProfile T x y = pairProfile T y x

def converse {L : Signature} {M : Type v} {T : BoolTable L M}
    {i j : UnaryName T} (a : PairAtom T i j) : PairAtom T j i :=
  ⟨swapProfile a.val, by
    rcases a.property with ⟨x,y,hxy,ha⟩
    refine ⟨y,x,Ne.symm hxy,?_⟩
    rw [← pairProfile_swap,ha]⟩

@[simp] theorem converse_converse {L : Signature} {M : Type v} {T : BoolTable L M}
    {i j : UnaryName T} (a : PairAtom T i j) : converse (converse a) = a := by
  apply Subtype.ext
  exact swapProfile_swap _

noncomputable def colour {L : Signature} {M : Type v} (T : BoolTable L M)
    {i j : UnaryName T} (x : Carrier T i) (y : Carrier T j) : Option (PairAtom T i j) := by
  classical
  exact if h : x.val = y.val then none
    else some ⟨pairProfile T x.val y.val,⟨x,y,h,rfl⟩⟩

theorem colour_none_iff {L : Signature} {M : Type v} (T : BoolTable L M)
    {i j : UnaryName T} (x : Carrier T i) (y : Carrier T j) :
    colour T x y = none ↔ (⟨i,x⟩ : Sigma (Carrier T)) = ⟨j,y⟩ := by
  classical
  unfold colour
  by_cases h : x.val = y.val
  · simp only [h, dite_true, true_iff]
    exact (pack T).symm.injective h
  · simp only [h, dite_false, Option.some_ne_none, false_iff]
    intro he
    exact h (congrArg (pack T).symm he)

theorem colour_some_iff {L : Signature} {M : Type v} (T : BoolTable L M)
    {i j : UnaryName T} (x : Carrier T i) (y : Carrier T j) (a : PairAtom T i j) :
    colour T x y = some a ↔ x.val ≠ y.val ∧ pairProfile T x.val y.val = a.val := by
  classical
  unfold colour
  split_ifs with h
  · simp [h]
  · simp only [Option.some.injEq,Subtype.ext_iff]
    exact (and_iff_right h).symm

noncomputable def source {L : Signature} {M : Type v} (T : BoolTable L M)
    (hsym : SameSortSymmetric T) : AtomicSource (UnaryName T) (Carrier T) where
  Atom := PairAtom T
  finiteSort := inferInstance
  finiteAtom _ _ := inferInstance
  nonemptySort _ := inferInstance
  conv := converse
  conv_invol := converse_converse
  symmetricLoop a := by
    apply Subtype.ext
    rcases a.property with ⟨x,y,hxy,ha⟩
    change swapProfile a.val = a.val
    rw [← ha,pairProfile_swap]
    exact (hsym x.val y.val (x.property.trans y.property.symm)).symm
  colour := colour T
  colour_none_iff := colour_none_iff T
  colour_swap x y a := by
    rw [colour_some_iff,colour_some_iff]
    constructor
    · rintro ⟨hne,hp⟩
      refine ⟨Ne.symm hne,?_⟩
      change pairProfile T y.val x.val = swapProfile a.val
      rw [← pairProfile_swap,hp]
    · rintro ⟨hne,hp⟩
      refine ⟨Ne.symm hne,?_⟩
      change pairProfile T y.val x.val = swapProfile a.val at hp
      have h := congrArg swapProfile hp
      simpa using h
  realized a := by
    rcases a.property with ⟨x,y,hxy,ha⟩
    exact ⟨x,y,(colour_some_iff T x y a).mpr ⟨hxy,ha⟩⟩

/-- Two full realizations have the very same typed unary owners. -/
theorem pack_owner_embedding {L : Signature} {V : Type w} {M : Type v}
    {A : BoolTable L V} {T : BoolTable L M} (p q : Embedding A T) (x : V) :
    (pack T (p.point x)).1 = (pack T (q.point x)).1 := by
  apply Subtype.ext
  exact (unaryProfile_embedding p x).trans (unaryProfile_embedding q x).symm

def tagCode {L : Signature} {M : Type v} (T : BoolTable L M)
    (c : Σ i : UnaryName T, Σ j : UnaryName T, Option (PairAtom T i j)) :
    Profile L 1 × Profile L 1 × Option (Profile L 2) :=
  (c.1.val,c.2.1.val,c.2.2.map Subtype.val)

theorem tagCode_injective {L : Signature} {M : Type v} (T : BoolTable L M) :
    Function.Injective (tagCode T) := by
  rintro ⟨i,j,c⟩ ⟨i',j',c'⟩ h
  have hi : i = i' := Subtype.ext (congrArg Prod.fst h)
  subst i'
  have hj : j = j' := Subtype.ext (congrArg (fun t => t.2.1) h)
  subst j'
  have hc : c.map Subtype.val = c'.map Subtype.val := congrArg (fun t => t.2.2) h
  have hcc : c = c' := by
    cases c <;> cases c' <;> simp_all [Subtype.ext_iff]
  subst c'
  rfl

theorem tagCode_pack {L : Signature} {M : Type v} (T : BoolTable L M)
    (hsym : SameSortSymmetric T) (x y : M) :
    tagCode T (taggedColour (source T hsym) (pack T x) (pack T y)) =
      (unaryProfile T x, unaryProfile T y,
        if x = y then none else some (pairProfile T x y)) := by
  classical
  by_cases h : x = y <;> simp [tagCode,taggedColour,source,pack,colour,h]

/-- Literal pair-chart independence from the chosen full realization. -/
theorem pack_taggedColour_embedding {L : Signature} {V : Type w} {M : Type v}
    {A : BoolTable L V} {T : BoolTable L M} (hsym : SameSortSymmetric T)
    (p q : Embedding A T) (x y : V) :
    taggedColour (source T hsym) (pack T (p.point x)) (pack T (p.point y)) =
      taggedColour (source T hsym) (pack T (q.point x)) (pack T (q.point y)) := by
  apply tagCode_injective T
  rw [tagCode_pack,tagCode_pack]
  simp only [unaryProfile_embedding,pairProfile_embedding,p.injective.eq_iff,
    q.injective.eq_iff]

/-- Identity colours still recover every repeated old tuple via the unary
profile. Thus the pair reduct never drops the diagonal atomic data. -/
theorem pairProfile_of_taggedColour_eq {L : Signature} {M : Type v}
    (T : BoolTable L M) (hsym : SameSortSymmetric T) {x y z w : M}
    (h : taggedColour (source T hsym) (pack T x) (pack T y) =
      taggedColour (source T hsym) (pack T z) (pack T w)) :
    pairProfile T x y = pairProfile T z w := by
  classical
  have hc := congrArg (tagCode T) h
  rw [tagCode_pack,tagCode_pack] at hc
  have hu : unaryProfile T x = unaryProfile T z := congrArg Prod.fst hc
  have hp := congrArg (fun t => t.2.2) hc
  by_cases hxy : x = y
  · subst y
    have hzw : z = w := by
      by_contra hzw
      simp only [if_pos rfl,if_neg hzw] at hp
      cases hp
    subst w
    simp only [pairProfile_self,hu]
  · have hzw : z ≠ w := by
      intro hzw
      simp only [if_neg hxy,if_pos hzw] at hp
      cases hp
    simpa only [if_neg hxy,if_neg hzw,Option.some.injEq] using hp

end CCO.FullPhaseLift.Canonical
