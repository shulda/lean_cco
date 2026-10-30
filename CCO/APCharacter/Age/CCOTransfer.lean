import CCO.APCharacter.Age.Reasonableness

/-! Semantic CCO passes to the constructed homogeneous marked limit by
finite-age witnesses. Cycle witnesses may come from unrelated source seed
markings; ONE complete finite marked image is embedded only at the end. -/
universe u v w t
namespace CCO.APCharacter.Age
open OwnerTransversal.CountableColour
open FirstOrder FirstOrder.Language
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
noncomputable section
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) {M : MaskData S}
variable (completion : CompletionProperty S M)

/-- A finite tuple, with possible repetitions, comes from ONE actual
finite chart of the direct-limit chain. -/
theorem finite_tuple_names {n : ℕ} (x : Fin n → Limit S H completion) :
    ∃ C : Chart S M, ∃ y : Fin n → Fin C.size,
      (∀ p, (limitCoding S H completion).table.owner (x p) = C.table.owner (y p)) ∧
      ∀ p q, (limitCoding S H completion).table.colour (x p) (x q) =
        C.table.colour (y p) (y q) := by
  let D := data S H completion
  obtain ⟨i,y,hy⟩ := DirectLimit.exists_quotient_mk'_sigma_mk'_eq
    (fun i => D.Carrier (D.stage i)) D.chain x
  have hx : x = (D.intoLimit i) ∘ y := hy
  let C := D.stage i
  letI := C.structure
  have hn := C.table.coding.embedding_preserves (limitCoding S H completion) (D.intoLimit i)
  refine ⟨C,y,?_,?_⟩
  · intro p
    rw [hx]
    exact (hn.1 (y p)).trans (Table.coding_table_owner C.table (y p))
  · intro p q
    rw [hx]
    exact (hn.2 (y p) (y q)).trans (Table.coding_table_colour C.table (y p) (y q))

/-- Dependent sort casts preserve exactly the original specified atom. -/
theorem colour_of_tagged {i j : ι} (p q : Sigma X) (hi : p.1 = i) (hj : q.1 = j)
    (a : S.Atom i j) (h : taggedColour S p q = ⟨i,j,some a⟩) :
    S.colour (hi ▸ p.2) (hj ▸ q.2) = some a := by
  rcases p with ⟨k,x⟩
  rcases q with ⟨l,y⟩
  cases hi
  cases hj
  exact eq_of_heq ((Sigma.mk.inj_iff.mp (eq_of_heq (Sigma.mk.inj_iff.mp h).2)).2)

variable {V : Type} (D : PartialDiagram S V) (bits : V → Bit)

def CycleRealizes (K : SimpleCycle D) : Prop :=
  ∃ point : Fin K.length → Limit S H completion,
    (∀ p, (limitCoding S H completion).table.owner (point p) =
      ownerEquiv S (D.vertexSort (K.vertices p),bits (K.vertices p))) ∧
    ∀ p a, D.edge (K.vertices p) (K.vertices (cyclicNext K.length_pos p))
        (K.next_ne p) = some a →
      (limitCoding S H completion).table.colour (point p)
        (point (cyclicNext K.length_pos p)) =
        colourEquiv S ⟨D.vertexSort (K.vertices p),
          D.vertexSort (K.vertices (cyclicNext K.length_pos p)),some a⟩

def DiagramRealizes : Prop :=
  ∃ point : V → Limit S H completion,
    (∀ x, (limitCoding S H completion).table.owner (point x) =
      ownerEquiv S (D.vertexSort x,bits x)) ∧
    ∀ x y h a, D.edge x y h = some a →
      (limitCoding S H completion).table.colour (point x) (point y) =
        colourEquiv S ⟨D.vertexSort x,D.vertexSort y,some a⟩

/-- A marked-limit cycle witness gives an actual OLD cycle homomorphism
through one finite chain chart, with no common seed required across cycles. -/
theorem old_cycle (K : SimpleCycle D)
    (hK : CycleRealizes S H completion D bits K) : CycleHom K := by
  obtain ⟨p,ho,hc⟩ := hK
  obtain ⟨C,q,hqo,hqc⟩ := finite_tuple_names S H completion p
  have hs (i : Fin K.length) : (C.point (q i)).1 = D.vertexSort (K.vertices i) := by
    have he : ownerEquiv S ((C.point (q i)).1,C.bits (q i)) =
        ownerEquiv S (D.vertexSort (K.vertices i),bits (K.vertices i)) :=
      (congrArg (fun T : Table S (Fin C.size) => T.owner (q i)) C.table_eq).symm.trans
        ((hqo i).symm.trans (ho i))
    exact congrArg Prod.fst ((ownerEquiv S).injective he)
  refine ⟨fun i => hs i ▸ (C.point (q i)).2,?_⟩
  intro i a ha
  apply colour_of_tagged S _ _ (hs i) (hs (cyclicNext K.length_pos i)) a
  apply (colourEquiv S).injective
  exact (congrArg (fun T : Table S (Fin C.size) =>
      T.colour (q i) (q (cyclicNext K.length_pos i))) C.table_eq).symm.trans
    ((hqc i (cyclicNext K.length_pos i)).symm.trans (hc i a ha))

/-- The constructed WHOLE homogeneous marked limit has semantic CCO in
its literal named unary/binary presentation. Each cycle may use a separate
finite chart; the conclusion is ONE simultaneous whole-network witness. -/
theorem marked_cco (legal : M.LocalLegal D bits)
    (cycles : ∀ K : SimpleCycle D, CycleRealizes S H completion D bits K) :
    DiagramRealizes S H completion D bits := by
  obtain ⟨F,mark,hm,he⟩ := completion D bits legal
    (fun K => old_cycle S H completion D bits K (cycles K))
  letI := D.finite_type
  let T := FiniteImage.table F mark
  have hT : Realized S M T := FiniteImage.realized F mark hm
  let C := chartOf S T hT
  letI := T.toStructure
  letI := C.structure
  let iso := chartOfEquiv S T hT
  have hnames := T.embedding_preserves C.table iso.toEmbedding
  obtain ⟨e,ho,hc⟩ := chart_names S H completion C
  let point : V → Limit S H completion := fun x => e (iso (Quotient.mk _ x))
  refine ⟨point,?_,?_⟩
  · intro x
    have hx := (ho (iso (Quotient.mk _ x))).trans (hnames.1 (Quotient.mk _ x))
    change (limitCoding S H completion).table.owner (point x) = _ at hx ⊢
    apply hx.trans
    change ownerEquiv S (D.vertexSort x,mark (F.image x)) = _
    rw [he]
  · intro x y h a ha
    have hxy := (hc (iso (Quotient.mk _ x)) (iso (Quotient.mk _ y))).trans
      (hnames.2 (Quotient.mk _ x) (Quotient.mk _ y))
    change (limitCoding S H completion).table.colour (point x) (point y) = _ at hxy ⊢
    apply hxy.trans
    change colourEquiv S (taggedColour S (F.image x) (F.image y)) = _
    apply congrArg (colourEquiv S)
    change (⟨D.vertexSort x,D.vertexSort y,S.colour (F.point x) (F.point y)⟩ : Colour S) = _
    rw [F.preserves_edge x y h a ha]

end
end CCO.APCharacter.Age
