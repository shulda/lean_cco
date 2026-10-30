import CCO.APCharacter.Age.Realized
import CCO.APCharacter.Rank.Source

/-! The canonical unary refinement on the SAME original carriers, pulled
back from the actual marked limit along a proved old-reduct identification.
The identification is an internal interface: the receiving source constructs
it from actual finite extension/back-and-forth, not a principal hypothesis. -/
universe u v w t
namespace CCO.APCharacter.SourceAge.UnarySource
open OwnerTransversal.CountableColour
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {M : MaskData S}
variable {completion : Age.CompletionProperty S M}
noncomputable section

structure Identification (S : AtomicSource.{u,v,w} ι X) (H : HomogeneousSource S G)
    {M : MaskData S} (completion : Age.CompletionProperty S M) where
  equiv : Sigma X ≃ Age.Limit S H completion
  owner_sort : ∀ x, ((Age.ownerEquiv S).symm
    ((Age.limitCoding S H completion).table.owner (equiv x))).1 = x.1
  colour_eq : ∀ x y, (Age.colourEquiv S).symm
    ((Age.limitCoding S H completion).table.colour (equiv x) (equiv y)) = taggedColour S x y

variable (I : Identification S H completion)

def mark (x : Sigma X) : Bit := ((Age.ownerEquiv S).symm
  ((Age.limitCoding S H completion).table.owner (I.equiv x))).2

theorem owner_eq (x : Sigma X) :
    (Age.limitCoding S H completion).table.owner (I.equiv x) = Age.ownerEquiv S (x.1,mark I x) := by
  apply (Age.ownerEquiv S).symm.injective
  rw [Equiv.symm_apply_apply]
  exact Prod.ext (I.owner_sort x) rfl

theorem colour_eq (x y : Sigma X) :
    (Age.limitCoding S H completion).table.colour (I.equiv x) (I.equiv y) =
      Age.colourEquiv S (taggedColour S x y) := by
  exact ((Age.colourEquiv S).symm_apply_eq).mp (I.colour_eq x y)

/-- Every finite tuple, including repetitions, has ONE actual finite marked
old chart with the pulled-back marks and every literal old ordered colour. -/
theorem finite_chart {n : ℕ} (point : Fin n → Sigma X) :
    ∃ C : Age.Chart S M, ∃ q : Fin n → Fin C.size,
      (∀ i, mark I (point i) = C.bits (q i)) ∧
      ∀ i j, taggedColour S (point i) (point j) = taggedColour S (C.point (q i)) (C.point (q j)) := by
  obtain ⟨C,q,ho,hc⟩ := Age.finite_tuple_names S H completion (I.equiv ∘ point)
  refine ⟨C,q,?_,?_⟩
  · intro i
    have he := (ho i).trans (congrArg (fun T : Age.Table S (Fin C.size) => T.owner (q i)) C.table_eq)
    have hh := congrArg (fun b => ((Age.ownerEquiv S).symm b).2) he
    change mark I (point i) = ((Age.ownerEquiv S).symm (Age.ownerEquiv S ((C.point (q i)).1,C.bits (q i)))).2 at hh
    simpa only [Equiv.symm_apply_apply] using hh
  · intro i j
    apply (Age.colourEquiv S).injective
    exact (colour_eq I (point i) (point j)).symm.trans
      ((hc i j).trans (congrArg (fun T : Age.Table S (Fin C.size) => T.colour (q i) (q j)) C.table_eq))

/-- Valid bits and ALL old-colour masks are inherited from actual finite
marked-age witnesses, never supplied as an extra global marking premise. -/
theorem global_marking : M.GlobalMarking (mark I) := by
  constructor
  · intro x
    let point : Fin 1 → Sigma X := fun _ => x
    obtain ⟨C,q,hm,hc⟩ := finite_chart I point
    have hlegal := Age.legal_of_names S M
      (⟨fun i => C.legal.1 (q i),fun i j => C.legal.2 (q i) (q j)⟩ :
        Age.Legal S M (C.point ∘ q) (C.bits ∘ q)) hc
    rw [show mark I x = C.bits (q 0) from hm 0]
    exact hlegal.1 0
  · intro x y
    let point : Fin 2 → Sigma X := ![x,y]
    obtain ⟨C,q,hm,hc⟩ := finite_chart I point
    have hlegal := Age.legal_of_names S M
      (⟨fun i => C.legal.1 (q i),fun i j => C.legal.2 (q i) (q j)⟩ :
        Age.Legal S M (C.point ∘ q) (C.bits ∘ q)) hc
    have hm0 : mark I x = C.bits (q 0) := hm 0
    have hm1 : mark I y = C.bits (q 1) := hm 1
    rw [hm0,hm1]
    exact hlegal.2 0 1

abbrev β (_I : Identification S H completion) (i : ι) := {ε : Bit // M.validBit i ε}
instance betaFinite (i : ι) : Finite (β I i) := inferInstance
noncomputable instance betaFintype (i : ι) : Fintype (β I i) := Fintype.ofFinite _

def tag (i : ι) (x : X i) : β I i := ⟨mark I ⟨i,x⟩,(global_marking I).1 ⟨i,x⟩⟩

/-- EVERY valid child is inhabited by an actual named singleton chart in
this SAME marked limit, transferred back through the proved reduct bijection. -/
theorem inhabited : ∀ c : Rank.Child (β I), Nonempty (Rank.Point (β I) (tag I) c) := by
  intro c
  classical
  let x : X c.1 := Classical.choice (S.nonemptySort c.1)
  let point : Fin 1 → Sigma X := fun _ => ⟨c.1,x⟩
  let bits : Fin 1 → Bit := fun _ => c.2.val
  have legal : Age.Legal S M point bits := by
    refine ⟨fun _ => c.2.property,?_⟩
    intro a b
    have he : S.colour x x = none := (S.colour_none_iff x x).mpr rfl
    change M.allowed (S.colour x x) c.2.val c.2.val
    rw [he]
    exact (M.identity c.1 c.2.val c.2.val).mpr ⟨rfl,c.2.property⟩
  obtain ⟨f,ho,_⟩ := Age.embed_realized S H completion point bits
    (fun a b _ => Subsingleton.elim a b) legal
  let p := I.equiv.symm (f 0)
  have he : ((Age.ownerEquiv S).symm ((Age.limitCoding S H completion).table.owner (I.equiv p))) =
      (c.1,c.2.val) := by
    rw [I.equiv.apply_symm_apply,ho]
    exact (Age.ownerEquiv S).symm_apply_apply _
  have hs : p.1 = c.1 := (I.owner_sort p).symm.trans (congrArg Prod.fst he)
  have hb : mark I p = c.2.val := congrArg Prod.snd he
  rcases c with ⟨i,b⟩
  rcases p with ⟨j,y⟩
  change j = i at hs
  subst j
  refine ⟨⟨y,?_⟩⟩
  apply Subtype.ext
  exact hb

abbrev source := Rank.source S (β I) (tag I) (inhabited I)

instance countable_child [∀ i, Countable (X i)] (c : Rank.Child (β I)) :
    Countable (Rank.Point (β I) (tag I) c) := inferInstance

end
end CCO.APCharacter.SourceAge.UnarySource
