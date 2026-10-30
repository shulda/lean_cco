import CCO.APCharacter.Age.CCOTransfer

/-! The homogeneous limit realizes precisely actual finite old-age objects
with legal bits. In particular genuine phase-one witnesses, including both
children of an active sort, survive as literal named vertices and pairs. -/
universe u v w t
namespace CCO.APCharacter.Age
open OwnerTransversal.CountableColour
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
noncomputable section
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) {M : MaskData S}
variable (completion : CompletionProperty S M)

/-- Every finite complete induced old object carrying legal bits embeds
with the SAME literal unary and binary names in the homogeneous limit. -/
theorem embed_realized {V : Type} [Finite V] (point : V → Sigma X) (bits : V → Bit)
    (hp : Function.Injective point) (legal : Legal S M point bits) :
    ∃ f : V ↪ Limit S H completion,
      (∀ x, (limitCoding S H completion).table.owner (f x) =
        ownerEquiv S ((point x).1,bits x)) ∧
      ∀ x y, (limitCoding S H completion).table.colour (f x) (f y) =
        colourEquiv S (taggedColour S (point x) (point y)) := by
  let T := table S point bits
  have hT : Realized S M T := ⟨point,bits,hp,legal,rfl⟩
  let C := chartOf S T hT
  letI := T.toStructure
  letI := C.structure
  let iso := chartOfEquiv S T hT
  have hn := T.embedding_preserves C.table iso.toEmbedding
  obtain ⟨e,ho,hc⟩ := chart_names S H completion C
  refine ⟨iso.toEquiv.toEmbedding.trans e,?_,?_⟩
  · intro x
    exact (ho (iso x)).trans (hn.1 x)
  · intro x y
    exact (hc (iso x) (iso y)).trans (hn.2 x y)

/-- An injective finite tuple factors through an actual finite chain
chart injectively, including empty and singleton tuples. -/
theorem finite_tuple_injective_names {n : ℕ} (point : Fin n → Limit S H completion)
    (hp : Function.Injective point) :
    ∃ C : Chart S M, ∃ q : Fin n ↪ Fin C.size,
      (∀ i, (limitCoding S H completion).table.owner (point i) = C.table.owner (q i)) ∧
      ∀ i j, (limitCoding S H completion).table.colour (point i) (point j) =
        C.table.colour (q i) (q j) := by
  let D := data S H completion
  obtain ⟨k,y,hy⟩ := FirstOrder.Language.DirectLimit.exists_quotient_mk'_sigma_mk'_eq
    (fun k => D.Carrier (D.stage k)) D.chain point
  have hx : point = (D.intoLimit k) ∘ y := hy
  have hY : Function.Injective y := by
    intro i j he
    apply hp
    rw [hx]
    exact congrArg (D.intoLimit k) he
  let C := D.stage k
  letI := C.structure
  have hn := C.table.coding.embedding_preserves (limitCoding S H completion) (D.intoLimit k)
  refine ⟨C,⟨y,hY⟩,?_,?_⟩
  · intro i
    rw [hx]
    exact (hn.1 (y i)).trans (Table.coding_table_owner C.table (y i))
  · intro i j
    rw [hx]
    exact (hn.2 (y i) (y j)).trans (Table.coding_table_colour C.table (y i) (y j))

/-- Marked finite objects in the limit do not acquire arbitrary old
colour assignments: an injective tuple has an injective actual OLD witness. -/
theorem finite_old_witness {n : ℕ} (point : Fin n → Limit S H completion)
    (hp : Function.Injective point) :
    ∃ (old : Fin n → Sigma X) (bits : Fin n → Bit), Function.Injective old ∧
      Legal S M old bits ∧
      (∀ i, (limitCoding S H completion).table.owner (point i) =
        ownerEquiv S ((old i).1,bits i)) ∧
      ∀ i j, (limitCoding S H completion).table.colour (point i) (point j) =
        colourEquiv S (taggedColour S (old i) (old j)) := by
  obtain ⟨C,q,ho,hc⟩ := finite_tuple_injective_names S H completion point hp
  exact ⟨C.point ∘ q,C.bits ∘ q,C.point_injective.comp q.injective,
    ⟨fun i => C.legal.1 (q i),fun i j => C.legal.2 (q i) (q j)⟩,
    fun i => (ho i).trans (congrArg (fun T : Table S (Fin C.size) => T.owner (q i)) C.table_eq),
    fun i j => (hc i j).trans (congrArg (fun T : Table S (Fin C.size) => T.colour (q i) (q j)) C.table_eq)⟩

end
end CCO.APCharacter.Age
