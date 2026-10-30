import CCO.FullPhaseLift.Marked.Fraisse
import CCO.FullPhaseLift.BinarySource.FullReductBackAndForth
import CCO.FullPhaseLift.BinarySource.FullAlignment

/-! The actual full old reduct of the constructed full marked limit.
Finite age witnesses, same-map reasonableness, and genuine full
homogeneity supply the two full finite extensions. Every old Bool tuple
is retained; no binary isomorphism is used for a higher relation. -/

open scoped FirstOrder
universe u v w m
namespace CCO.FullPhaseLift.BinarySource.FullReduct
open Canonical APCharacter
noncomputable section
variable {L : Signature} {M : Type m} (U : BoolTable L M)
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable (pack : M ≃ Sigma X) (mask : MaskData S)
variable (sap : Marked.StrongAmalgamation U S pack mask)

abbrev Carrier := Marked.Limit U S pack mask sap

def expandedTable : BoolTable (Marked.addBit L) (Carrier U S pack mask sap) :=
  ofFirstOrder (inferInstance : (Marked.addBit L).firstOrder.Structure (Carrier U S pack mask sap))

def oldTable : BoolTable L (Carrier U S pack mask sap) :=
  Marked.oldTable (expandedTable U S pack mask sap)

def bits : Carrier U S pack mask sap → Bit :=
  Marked.bits (expandedTable U S pack mask sap)

private theorem cast_embedding_apply {K : FirstOrder.Language} {A B : Type}
    {a : K.Structure A} {s t : K.Structure B} (h : s = t)
    (f : @FirstOrder.Language.Embedding K A B a s) (x : A) :
    (cast (congrArg (fun st => @FirstOrder.Language.Embedding K A B a st) h) f) x = f x := by
  cases h
  rfl

def intoLimit {V : Type} {T : BoolTable (Marked.addBit L) V}
    (e : Canonical.Embedding T (expandedTable U S pack mask sap)) :
    @FirstOrder.Language.Embedding (Marked.addBit L).firstOrder V
      (Carrier U S pack mask sap) (toFirstOrder T) inferInstance := by
  have hs := toFirstOrder_ofFirstOrder
    (inferInstance : (Marked.addBit L).firstOrder.Structure (Carrier U S pack mask sap))
  exact cast (congrArg (fun st => @FirstOrder.Language.Embedding
    (Marked.addBit L).firstOrder V (Carrier U S pack mask sap) (toFirstOrder T) st) hs)
    (embeddingToFirstOrder e)

def fromLimit {V : Type} {T : BoolTable (Marked.addBit L) V}
    (e : @FirstOrder.Language.Embedding (Marked.addBit L).firstOrder V
      (Carrier U S pack mask sap) (toFirstOrder T) inferInstance) :
    Canonical.Embedding T (expandedTable U S pack mask sap) := by
  have hs := toFirstOrder_ofFirstOrder
    (inferInstance : (Marked.addBit L).firstOrder.Structure (Carrier U S pack mask sap))
  exact embeddingOfFirstOrder (cast (congrArg (fun st => @FirstOrder.Language.Embedding
    (Marked.addBit L).firstOrder V (Carrier U S pack mask sap) (toFirstOrder T) st) hs.symm) e)

theorem fromLimit_point {V : Type} {T : BoolTable (Marked.addBit L) V}
    (e : @FirstOrder.Language.Embedding (Marked.addBit L).firstOrder V
      (Carrier U S pack mask sap) (toFirstOrder T) inferInstance) (x : V) :
    (fromLimit U S pack mask sap e).point x = e x := by
  exact cast_embedding_apply (toFirstOrder_ofFirstOrder
    (inferInstance : (Marked.addBit L).firstOrder.Structure (Carrier U S pack mask sap))).symm e x

theorem intoLimit_point {V : Type} {T : BoolTable (Marked.addBit L) V}
    (e : Canonical.Embedding T (expandedTable U S pack mask sap)) (x : V) :
    intoLimit U S pack mask sap e x = e.point x := by
  exact cast_embedding_apply (toFirstOrder_ofFirstOrder
    (inferInstance : (Marked.addBit L).firstOrder.Structure (Carrier U S pack mask sap)))
    (embeddingToFirstOrder e) x

theorem finite_old_witness {n : ℕ} (p : Fin n ↪ Carrier U S pack mask sap) :
    ∃ q : Canonical.Embedding (pullback (oldTable U S pack mask sap) p) U,
      Age.Legal S mask (pack ∘ q.point) (bits U S pack mask sap ∘ p) := by
  let E := expandedTable U S pack mask sap
  let T := pullback E p
  letI := toFirstOrder T
  let e : Canonical.Embedding T E := embeddingOf p p.injective (fun _ _ => rfl)
  obtain ⟨C,⟨eqv⟩⟩ := ((Marked.data U S pack mask sap).finite_age (Fin n)).mp
    ⟨intoLimit U S pack mask sap e⟩
  let iso : Canonical.Iso T (Marked.table C.old.full C.bits) := isoOfFirstOrder eqv
  have h : Marked.Realized U S pack mask (Marked.oldTable T) (Marked.bits T) := by
    apply Marked.realized_of_embedding U S pack mask C
    rw [Marked.table_oldTable_bits]
    exact iso.toEmbedding
  exact h

theorem back_extension (hom : (toRelational U).Homogeneous) :
    FullFiniteExtension (oldTable U S pack mask sap) U := by
  intro n k j p q hfull
  obtain ⟨r,hr⟩ := finite_old_witness U S pack mask sap p
  have heq : ∀ x y, r.point (j x) = r.point (j y) ↔ q x = q y := by
    intro x y
    rw [r.injective.eq_iff,j.injective.eq_iff,q.injective.eq_iff]
  have hrel : ∀ {a} (R : L.language.Rel a) xs,
      (toRelational U).rel R ((r.point ∘ j) ∘ xs) ↔ (toRelational U).rel R (q ∘ xs) := by
    intro a R xs
    rcases R with ⟨r',ha⟩
    subst a
    have he := embedding_read r r' (j ∘ xs)
    change U r' ((r.point ∘ j) ∘ xs) =
      (oldTable U S pack mask sap) r' ((p ∘ j) ∘ xs) at he
    change (U r' ((r.point ∘ j) ∘ xs) = true) ↔ U r' (q ∘ xs) = true
    rw [he,← hfull]
  obtain ⟨a,ha⟩ := full_tuple_homogeneous (toRelational U) hom (r.point ∘ j) q heq hrel
  let f : Fin k ↪ M := (⟨r.point,r.injective⟩ : Fin k ↪ M).trans a.point.toEmbedding
  refine ⟨f,?_,ha⟩
  intro r' xs
  exact (iso_read a r' (r.point ∘ xs)).trans (embedding_read r r' xs)

theorem forth_extension (names : Marked.PairFaithful U S pack)
    (seeds : mask.FiniteSeedExtension) :
    FullFiniteExtension U (oldTable U S pack mask sap) := by
  intro n k j p q hfull
  obtain ⟨r,hr⟩ := finite_old_witness U S pack mask sap q
  let A := pullback (oldTable U S pack mask sap) q
  let B := pullback U p
  let b : Fin n → Bit := bits U S pack mask sap ∘ q
  let pBase : Canonical.Embedding A U := embeddingOf (p ∘ j)
    (p.injective.comp j.injective) (fun r xs => (hfull r xs).symm)
  have hpairs (x y : Fin n) :
      taggedColour S ((pack ∘ p) (j x)) ((pack ∘ p) (j y)) =
        taggedColour S ((pack ∘ r.point) x) ((pack ∘ r.point) y) :=
    names r pBase x y
  obtain ⟨targetBits,targetLegal,hbits,_⟩ :=
    Age.reasonable S mask seeds (pack ∘ r.point) (pack ∘ p) j b hr hpairs
  let e : Canonical.Embedding (Marked.table A b) (expandedTable U S pack mask sap) :=
    embeddingOf q q.injective (by
      intro r'
      refine Fin.cases ?_ (fun _ _ => rfl) r'
      intro xs
      exact (congrFun (congrFun (Marked.table_oldTable_bits
        (expandedTable U S pack mask sap)) 0) (q ∘ xs)).symm)
  let oldJ : Canonical.Embedding A B :=
    embeddingOf j j.injective (fun r xs => (hfull r xs).symm)
  let f : Canonical.Embedding (Marked.table A b) (Marked.table B targetBits) :=
    Marked.embedding oldJ hbits
  let pFull : Canonical.Embedding B U := embeddingOf p p.injective (fun _ _ => rfl)
  have targetRealized : Marked.Realized U S pack mask B targetBits := ⟨pFull,targetLegal⟩
  let C := Marked.chartOf U S pack mask B targetBits targetRealized
  let iso := Marked.chartOfIso U S pack mask B targetBits targetRealized
  letI := toFirstOrder (Marked.table A b)
  letI := toFirstOrder (Marked.table B targetBits)
  have hAge : (Marked.data U S pack mask sap).InAge (Fin k) :=
    ⟨C,⟨isoToFirstOrder iso⟩⟩
  obtain ⟨g,hg⟩ := (Marked.data U S pack mask sap).extensionProperty
    (Fin n) (Fin k) hAge (intoLimit U S pack mask sap e) (embeddingToFirstOrder f)
  let g' := fromLimit U S pack mask sap g
  let result : Fin k ↪ Carrier U S pack mask sap := g.toEmbedding
  refine ⟨result,?_,?_⟩
  · intro r' xs
    have h := embedding_read g' r'.succ xs
    change (oldTable U S pack mask sap) r' (g'.point ∘ xs) = U r' (p ∘ xs) at h
    have hp : g'.point = result := funext (fromLimit_point U S pack mask sap g)
    rwa [hp] at h
  · intro x
    have h := DFunLike.congr_fun hg x
    change g (j x) = intoLimit U S pack mask sap e x at h
    exact h.trans (intoLimit_point U S pack mask sap e x)

theorem empty_agreement :
    ∀ r (xs : Fin (L.arity r) → Fin 0),
      (oldTable U S pack mask sap) r (Fin.elim0 ∘ xs) = U r (Fin.elim0 ∘ xs) := by
  intro r xs
  let p : Fin 0 ↪ Carrier U S pack mask sap := ⟨Fin.elim0,fun x => Fin.elim0 x⟩
  obtain ⟨q,_⟩ := finite_old_witness U S pack mask sap p
  have h := embedding_read q r xs
  have hp : (p : Fin 0 → Carrier U S pack mask sap) = Fin.elim0 := funext (fun x => Fin.elim0 x)
  have hq : q.point = (Fin.elim0 : Fin 0 → M) := funext (fun x => Fin.elim0 x)
  change U r (q.point ∘ xs) = (oldTable U S pack mask sap) r (p ∘ xs) at h
  exact (congrArg ((oldTable U S pack mask sap) r)
    (congrArg (fun f => f ∘ xs) hp)).symm.trans
      (h.symm.trans (congrArg (U r) (congrArg (fun f => f ∘ xs) hq)))

/-- The resulting bijection preserves ALL old relation tuples and every
nullary truth, so it identifies the actual old FULL reduct with U. -/
theorem old_full_iso [Countable M] (hom : (toRelational U).Homogeneous)
    (names : Marked.PairFaithful U S pack) (seeds : mask.FiniteSeedExtension) :
    Nonempty (Canonical.Iso (oldTable U S pack mask sap) U) := by
  obtain ⟨e⟩ := fullIso_of_finiteExtension U (oldTable U S pack mask sap)
    (forth_extension U S pack mask sap names seeds) (back_extension U S pack mask sap hom)
    (empty_agreement U S pack mask sap)
  exact ⟨e.symm⟩

end
end CCO.FullPhaseLift.BinarySource.FullReduct
