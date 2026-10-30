import CCO.APCharacter.SourceAge.BackAndForth
import CCO.APCharacter.Age.Realized
import CCO.APCharacter.Age.Reasonableness

/-! Reasonableness and actual marked-limit extension prove the old reduct
isomorphic to the ORIGINAL source, including finite or empty carriers. -/
universe u v w t
namespace CCO.APCharacter.SourceAge
open OwnerTransversal.CountableColour
open scoped FirstOrder
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) {M : MaskData S}
variable (completion : Age.CompletionProperty S M)
noncomputable section

def decodedOwner (y : Age.Limit S H completion) : ι × Bit :=
  (Age.ownerEquiv S).symm ((Age.limitCoding S H completion).table.owner y)
def decodedColour (y z : Age.Limit S H completion) : Age.Colour S :=
  (Age.colourEquiv S).symm ((Age.limitCoding S H completion).table.colour y z)
def originalTable : Table ι (Age.Colour S) (Sigma X) where
  owner := Sigma.fst
  colour := taggedColour S
def reductTable : Table ι (Age.Colour S) (Age.Limit S H completion) where
  owner y := (decodedOwner S H completion y).1
  colour := decodedColour S H completion

theorem decoded_witness {n : ℕ} (p : Fin n → Age.Limit S H completion)
    (hp : Function.Injective p) :
    ∃ (old : Fin n → Sigma X) (bits : Fin n → Bit), Function.Injective old ∧
      Age.Legal S M old bits ∧
      (∀ i, decodedOwner S H completion (p i) = ((old i).1,bits i)) ∧
      ∀ i j, decodedColour S H completion (p i) (p j) = taggedColour S (old i) (old j) := by
  obtain ⟨old,bits,hi,hl,ho,hc⟩ := Age.finite_old_witness S H completion p hp
  refine ⟨old,bits,hi,hl,?_,?_⟩
  · intro i
    simp only [decodedOwner,ho,Equiv.symm_apply_apply]
  · intro i j
    simp only [decodedColour,hc,Equiv.symm_apply_apply]

/-- The limit's native FirstOrder structure is used; no copied table
structure is silently substituted in its extension property. -/
def intoLimit {V : Type} (T : Age.Table S V) (f : V ↪ Age.Limit S H completion)
    (ho : ∀ x, (Age.limitCoding S H completion).table.owner (f x) = T.owner x)
    (hc : ∀ x y, (Age.limitCoding S H completion).table.colour (f x) (f y) = T.colour x y) :
    @FirstOrder.Language.Embedding (Age.Language S) V (Age.Limit S H completion)
      T.toStructure inferInstance := by
  letI := T.toStructure
  exact {
    toFun := f
    inj' := f.injective
    map_fun' F := Empty.elim F
    map_rel' := by
      intro n r x
      cases r with
      | owner b =>
        rw [(Age.limitCoding S H completion).owner_tuple]
        exact (congrArg (· = b) (ho (x 0))).to_iff
      | colour c =>
        rw [(Age.limitCoding S H completion).colour_tuple]
        exact (congrArg (· = c) (hc (x 0) (x 1))).to_iff }

theorem back_extension :
    FiniteExtension (reductTable S H completion) (originalTable S) := by
  intro n m j p q ⟨ho,hc⟩
  obtain ⟨old,bits,hi,hl,hw,hcol⟩ := decoded_witness S H completion p p.injective
  have hnames : ∀ x y, taggedColour S (old (j x)) (old (j y)) = taggedColour S (q x) (q y) := by
    intro x y
    exact (hcol (j x) (j y)).symm.trans (hc x y).symm
  obtain ⟨g,hg⟩ := Age.align_finite S H (old ∘ j) q hnames
  let r : Fin m ↪ Sigma X := ⟨fun i => g • old i,(MulAction.injective g).comp hi⟩
  refine ⟨r,?_,?_,hg⟩
  · intro i
    exact (H.preserves_sort g (old i)).trans (congrArg Prod.fst (hw i)).symm
  · intro i k
    exact (H.preserves_colours g (old i) (old k)).trans (hcol i k).symm

theorem forth_extension (seeds : M.FiniteSeedExtension) :
    FiniteExtension (originalTable S) (reductTable S H completion) := by
  intro n m j p q ⟨ho,hc⟩
  obtain ⟨old,bits,hi,hl,hw,hcol⟩ := decoded_witness S H completion q q.injective
  have hnames : ∀ x y, taggedColour S (p (j x)) (p (j y)) = taggedColour S (old x) (old y) := by
    intro x y
    exact (hc x y).symm.trans (hcol x y)
  obtain ⟨targetBits,hlegal,he,_,_,_⟩ := Age.reasonable S M seeds old p j bits hl hnames
  let T := Age.table S old bits
  let U := Age.table S p targetBits
  letI := T.toStructure
  letI := U.toStructure
  let e : Fin n ↪[Age.Language S] Age.Limit S H completion :=
    intoLimit S H completion T q
      (fun x => by
        change (Age.limitCoding S H completion).table.owner (q x) = _
        apply (Age.ownerEquiv S).symm.injective
        simpa only [decodedOwner,T,Age.table,Equiv.symm_apply_apply] using hw x)
      (fun x y => by
        apply (Age.colourEquiv S).symm.injective
        simpa only [decodedColour,T,Age.table,Equiv.symm_apply_apply] using hcol x y)
  let f : Fin n ↪[Age.Language S] Fin m := T.embedding U j
    (fun x => by
      change Age.ownerEquiv S ((p (j x)).1,targetBits (j x)) = Age.ownerEquiv S ((old x).1,bits x)
      rw [he]
      exact congrArg (fun i => Age.ownerEquiv S (i,bits x))
        (congrArg (fun z : Age.Colour S => z.1) (hnames x x)))
    (fun x y => congrArg (Age.colourEquiv S) (hnames x y))
  let D := Age.data S H completion
  have hU : Age.Realized S M U := ⟨p,targetBits,p.injective,hlegal,rfl⟩
  have hB : D.InAge (Fin m) := ⟨Age.chartOf S U hU,⟨Age.chartOfEquiv S U hU⟩⟩
  obtain ⟨r,hr⟩ := D.extensionProperty (Fin n) (Fin m) hB e f
  have hn := U.coding.embedding_preserves (Age.limitCoding S H completion) r
  refine ⟨r.toEmbedding,?_,?_,?_⟩
  · intro i
    change (decodedOwner S H completion (r i)).1 = (p i).1
    simpa only [decodedOwner,U,Age.table,Equiv.symm_apply_apply,Table.coding_table_owner] using
      congrArg (fun c => ((Age.ownerEquiv S).symm c).1) (hn.1 i)
  · intro i k
    change decodedColour S H completion (r i) (r k) = taggedColour S (p i) (p k)
    simpa only [decodedColour,U,Age.table,Equiv.symm_apply_apply,Table.coding_table_colour] using
      congrArg (Age.colourEquiv S).symm (hn.2 i k)
  · intro i
    exact DFunLike.congr_fun hr i

/-- The old reduct equivalence is CONSTRUCTED from both finite extension
proofs. A homogeneous marked limit is never assumed to be a marking of M. -/
theorem old_reduct_equiv [∀ i, Countable (X i)] (seeds : M.FiniteSeedExtension) :
    ∃ e : Sigma X ≃ Age.Limit S H completion,
      (∀ x, (decodedOwner S H completion (e x)).1 = x.1) ∧
      ∀ x y, decodedColour S H completion (e x) (e y) = taggedColour S x y := by
  letI := S.finiteSort
  exact equiv_of_finiteExtension (originalTable S) (reductTable S H completion)
    (forth_extension S H completion seeds) (back_extension S H completion)

end
end CCO.APCharacter.SourceAge
