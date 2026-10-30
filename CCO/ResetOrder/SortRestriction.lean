import CCO.ResetOrder.Unary.FiniteAge

/-! C01--C06: actual full-language selected-sort restrictions. -/
universe u v
namespace CCO.ResetOrder.Unary
open CCO.UnarySupport
variable {L : Signature.{u}}

def ClosedSorts (I : Set L.Sorts) : Prop := ∀ F, L.input F ∈ I → L.output F ∈ I

def AllSorts (I : Set L.Sorts) (A : Object.{u,v} L) : Prop := ∀ x, A.data.sort x ∈ I

def selected (I : Set L.Sorts) (A : Object.{u,v} L) : Set A.Carrier := {x | A.data.sort x ∈ I}

theorem selected_closed (I : Set L.Sorts) (hI : ClosedSorts I) (A : Object.{u,v} L) :
    A.data.IsClosed (selected I A) := by
  intro F x hx y hy
  obtain ⟨hi,ho⟩ := A.data.func_sorted F x y hy
  change A.data.sort y ∈ I
  rw [ho]
  exact hI F (hi ▸ hx)

def restrict (I : Set L.Sorts) (hI : ClosedSorts I) (A : Object.{u,v} L) : Object.{u,v} L :=
  A.induce (selected I A) (selected_closed I hI A)

def restrictedAge (I : Set L.Sorts) (K : Age.{u,v} L) : Age.{u,v} L := fun A => K A ∧ AllSorts I A

theorem restrict_all (I : Set L.Sorts) (hI : ClosedSorts I) (A : Object.{u,v} L) :
    AllSorts I (restrict I hI A) := fun x => x.property

theorem restrict_mem {I : Set L.Sorts} (hI : ClosedSorts I) {K : Age.{u,v} L}
    (hK : Hereditary K) {A : Object.{u,v} L} (hA : K A) :
    restrictedAge I K (restrict I hI A) :=
  ⟨hK hA ⟨A.inclusion _ _⟩,restrict_all I hI A⟩

def factorSelected {I : Set L.Sorts} (hI : ClosedSorts I)
    {A C : Object.{u,v} L} (hA : AllSorts I A) (f : A.Emb C) : A.Emb (restrict I hI C) where
  point x := ⟨f.point x,by change C.data.sort (f.point x) ∈ I; rw [f.sort_eq]; exact hA x⟩
  sort_eq x := f.sort_eq x
  map_func F x y h := f.map_func F x y h
  map_rel R xs h := f.map_rel R xs h
  injective x y h := f.injective (congrArg Subtype.val h)
  reflect_func F x y hy := by
    obtain ⟨z,hz,he⟩ := f.reflect_func F x y.val hy
    exact ⟨z,hz,Subtype.ext he⟩
  reflect_rel R xs h := f.reflect_rel R xs h

@[simp] theorem factorSelected_point {I : Set L.Sorts} (hI : ClosedSorts I)
    {A C : Object.{u,v} L} (hA : AllSorts I A) (f : A.Emb C) (x : A.Carrier) :
    ((factorSelected hI hA f).point x).val = f.point x := rfl

def selectedEmbeddingEquiv {I : Set L.Sorts} (hI : ClosedSorts I)
    {A C : Object.{u,v} L} (hA : AllSorts I A) : A.Emb C ≃ A.Emb (restrict I hI C) where
  toFun := factorSelected hI hA
  invFun f := compose (C.inclusion _ _) f
  left_inv f := by apply hom_ext; intro x; rfl
  right_inv f := by apply hom_ext; intro x; apply Subtype.ext; rfl

theorem restriction_relation {I : Set L.Sorts} (hI : ClosedSorts I)
    (C : Object.{u,v} L) (R : L.Rel) (xs : Fin (L.arity R) → (restrict I hI C).Carrier) :
    (restrict I hI C).data.rel R xs ↔ C.data.rel R (Subtype.val ∘ xs) := Iff.rfl

theorem restriction_nullary_truth {I : Set L.Sorts} (hI : ClosedSorts I)
    (C : Object.{u,v} L) (R : L.Rel) (_hR : L.arity R = 0)
    (xs : Fin (L.arity R) → (restrict I hI C).Carrier) :
    (restrict I hI C).data.rel R xs ↔ C.data.rel R (Subtype.val ∘ xs) := Iff.rfl

theorem restricted_age_is_actual_image {I : Set L.Sorts} (hI : ClosedSorts I)
    {K : Age.{u,v} L} (hK : Hereditary K) (A : Object.{u,v} L) :
    restrictedAge I K A ↔ ∃C, K C ∧ Nonempty (Iso A.data (restrict I hI C).data) := by
  constructor
  · rintro ⟨hA,hAI⟩
    refine ⟨A,hA,⟨⟨factorSelected hI hAI (identity A.data),?_⟩⟩⟩
    intro x
    exact ⟨x.val,Subtype.ext rfl⟩
  · rintro ⟨C,hC,⟨e⟩⟩
    refine ⟨hK (restrict_mem hI hK hC).1 ⟨e.hom⟩,?_⟩
    intro x
    rw [← e.hom.sort_eq]
    exact (e.hom.point x).property

theorem restricted_hereditary {I : Set L.Sorts} {K : Age.{u,v} L}
    (hK : Hereditary K) : Hereditary (restrictedAge I K) := by
  rintro A B ⟨hA,hAI⟩ ⟨f⟩
  refine ⟨hK hA ⟨f⟩,?_⟩
  intro x
  rw [← f.sort_eq]
  exact hAI _

theorem restriction_ramsey {I : Set L.Sorts} (hI : ClosedSorts I) {K : Age.{u,v} L}
    (hK : Hereditary K) (ramsey : Ramsey K) : Ramsey (restrictedAge I K) := by
  intro A B hA hB k hk
  obtain ⟨C,hC,hArrow⟩ := ramsey A B hA.1 hB.1 k hk
  refine ⟨restrict I hI C,restrict_mem hI hK hC,?_⟩
  intro color
  obtain ⟨g,s,hs⟩ := hArrow (fun f => color (factorSelected hI hA.2 f))
  refine ⟨factorSelected hI hB.2 g,s,?_⟩
  intro f
  have he : compose (factorSelected hI hB.2 g) f = factorSelected hI hA.2 (compose g f) := by
    apply hom_ext
    intro x
    rfl
  rw [he]
  exact hs f

theorem restriction_jep {I : Set L.Sorts} (hI : ClosedSorts I) {K : Age.{u,v} L}
    (hK : Hereditary K) (jep : JEP K) : JEP (restrictedAge I K) := by
  intro A B hA hB
  obtain ⟨C,hC,⟨f⟩,⟨g⟩⟩ := jep A B hA.1 hB.1
  exact ⟨restrict I hI C,restrict_mem hI hK hC,
    ⟨factorSelected hI hA.2 f⟩,⟨factorSelected hI hB.2 g⟩⟩

theorem restriction_sap {I : Set L.Sorts} (hI : ClosedSorts I) {K : Age.{u,v} L}
    (hK : Hereditary K) (sap : SAP K) : SAP (restrictedAge I K) := by
  intro P A B hP hA hB i j
  obtain ⟨C,hC,f,g,hcomm,hstrong⟩ := sap P A B hP.1 hA.1 hB.1 i j
  refine ⟨restrict I hI C,restrict_mem hI hK hC,
    factorSelected hI hA.2 f,factorSelected hI hB.2 g,?_,?_⟩
  · intro p
    exact Subtype.ext (hcomm p)
  · intro a b he
    exact hstrong a b (congrArg Subtype.val he)

end CCO.ResetOrder.Unary
