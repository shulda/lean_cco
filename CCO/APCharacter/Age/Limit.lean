import CCO.APCharacter.Age.Amalgamation

/-! The actual marked Fraïssé limit. Its ordinary AP is the preceding
legwise-injective completion construction, so finite or empty old sources
are permitted and no strong amalgamation is assumed. -/
universe u v w t
namespace CCO.APCharacter.Age
open OwnerTransversal.CountableColour
open scoped FirstOrder
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
noncomputable section
variable {M : MaskData S}

def emptyEmbedding (C : Chart S M) :
    @FirstOrder.Language.Embedding (Language S) (Fin (emptyChart S M).size)
      (Fin C.size) (emptyChart S M).structure C.structure :=
  (emptyChart S M).table.embedding C.table
    ⟨Fin.elim0,fun x => Fin.elim0 x⟩ (fun x => Fin.elim0 x) (fun x => Fin.elim0 x)

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)

def data (completion : CompletionProperty S M) : OwnerTransversal.CountableAge.Data (Language S) where
  Chart := Chart S M
  Carrier C := Fin C.size
  finiteCarrier _ := inferInstance
  structureCarrier C := C.structure
  hereditary A _ _ C f := hereditary S C A f
  joint B C := by
    obtain ⟨Z,f,g,_⟩ := amalgamate S H completion (emptyChart S M) B C
      (emptyEmbedding S B) (emptyEmbedding S C)
    exact ⟨Z,⟨f⟩,⟨g⟩⟩
  amalgamate A B C f g := by
    letI := A.structure
    letI := B.structure
    letI := C.structure
    obtain ⟨Z,f',g',h⟩ := amalgamate S H completion A B C f g
    letI := Z.structure
    refine ⟨Z,f',g',?_⟩
    exact FirstOrder.Language.Embedding.ext h

abbrev Limit (completion : CompletionProperty S M) := (data S H completion).Limit

theorem homogeneous (completion : CompletionProperty S M) :
    (Language S).IsUltrahomogeneous (Limit S H completion) :=
  (data S H completion).homogeneous

theorem isFraisseLimit (completion : CompletionProperty S M) :
    FirstOrder.Language.IsFraisseLimit (data S H completion).ageClass (Limit S H completion) :=
  (data S H completion).isFraisseLimit

def limitCoding (completion : CompletionProperty S M) :
    Coding (B := OwnerCode S) (C := ColourCode S) (Limit S H completion) :=
  (data S H completion).limitCoding (fun C => C.table.coding)

/-- Homogeneity of the WHOLE expanded structure extends every finite
old-name/child-name preserving partial map, including repeated points. -/
theorem tuple_homogeneous (completion : CompletionProperty S M)
    {I : Type*} [Finite I] (source target : I → Limit S H completion)
    (he : ∀ i j, source i = source j ↔ target i = target j)
    (ho : ∀ i, (limitCoding S H completion).table.owner (source i) =
      (limitCoding S H completion).table.owner (target i))
    (hc : ∀ i j, (limitCoding S H completion).table.colour (source i) (source j) =
      (limitCoding S H completion).table.colour (target i) (target j)) :
    ∃ g : Limit S H completion ≃[Language S] Limit S H completion,
      ∀ i, g (source i) = target i :=
  (limitCoding S H completion).tuple_homogeneous (homogeneous S H completion)
    source target he ho hc

/-- Every ACTUAL marked finite chart embeds into the limit, so prescribed
nonempty child sorts and phase-one pairs pass to the homogeneous source. -/
theorem chart_embeds (completion : CompletionProperty S M) (C : Chart S M) :
    Nonempty (@FirstOrder.Language.Embedding (Language S) (Fin C.size)
      (Limit S H completion) C.structure inferInstance) :=
  (data S H completion).chart_embeds C

/-- Literal unary/binary names of a marked chart survive together in ONE
limit embedding. This will populate the two children of each odd gate. -/
theorem chart_names (completion : CompletionProperty S M) (C : Chart S M) :
    ∃ f : Fin C.size ↪ Limit S H completion,
      (∀ x, (limitCoding S H completion).table.owner (f x) = C.table.owner x) ∧
      ∀ x y, (limitCoding S H completion).table.colour (f x) (f y) = C.table.colour x y := by
  letI := C.structure
  obtain ⟨f⟩ := chart_embeds S H completion C
  have hn := C.table.coding.embedding_preserves (limitCoding S H completion) f
  refine ⟨f.toEmbedding,?_,?_⟩
  · intro x
    change (limitCoding S H completion).table.owner (f x) = _
    exact (hn.1 x).trans (Table.coding_table_owner C.table x)
  · intro x y
    change (limitCoding S H completion).table.colour (f x) (f y) = _
    exact (hn.2 x y).trans (Table.coding_table_colour C.table x y)

end
end CCO.APCharacter.Age
