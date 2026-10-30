import CCO.CloneSAP.Homogeneity
import CCO.AgeAP

universe u v w
namespace CCO.CloneSAP
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource ι X)

/-- Complete clone types are determined by the old complete type and real equality. -/
theorem colour_ext {i : ι} (x y x' y' : Carrier X i) (ho : S.colour x.1 y.1 = S.colour x'.1 y'.1)
    (hd : x = y ↔ x' = y') : colour S x y = colour S x' y' := by
  classical
  apply Option.ext
  intro a
  cases a with
  | inl a => simp only [colour_old_iff,ho]
  | inr e =>
    simp only [colour_clone_iff,Sigma.mk.injEq,heq_eq_eq,true_and]
    by_cases hn : S.colour x.1 y.1 = none
    · have hxy : x.1 = y.1 := eq_of_heq (Sigma.mk.inj ((S.colour_none_iff _ _).mp hn)).2
      have hxy' : x'.1 = y'.1 := eq_of_heq (Sigma.mk.inj ((S.colour_none_iff _ _).mp (ho.symm.trans hn))).2
      have hi : x.2 = y.2 ↔ x'.2 = y'.2 := by
        simpa only [Prod.ext_iff,hxy,hxy',true_and] using hd
      simpa only [hxy,hxy',true_and] using not_congr hi
    · have hxy : x.1 ≠ y.1 := by
        intro he; exact hn ((S.colour_none_iff _ _).mpr (by simpa only [he]))
      have hxy' : x'.1 ≠ y'.1 := by
        intro he; exact hn (ho.trans ((S.colour_none_iff _ _).mpr (by simpa only [he])))
      simp only [hxy,hxy',false_and]

/-- The corresponding statement for differently sorted ordered endpoints. -/
theorem tagged_reconstruct {p q r s : Sigma (Carrier X)}
    (ho : taggedColour S (owner p) (owner q) = taggedColour S (owner r) (owner s))
    (hd : p = q ↔ r = s) : taggedColour (source S) p q = taggedColour (source S) r s := by
  rcases p with ⟨i,x⟩
  rcases q with ⟨j,y⟩
  rcases r with ⟨k,z⟩
  rcases s with ⟨l,t⟩
  have hik : i = k := congrArg (fun a => a.1) ho
  have hjl : j = l := congrArg (fun a => a.2.1) ho
  subst k
  subst l
  have hc : S.colour x.1 y.1 = S.colour z.1 t.1 := by
    simpa only [taggedColour,owner,Sigma.mk.injEq,heq_eq_eq,true_and] using ho
  classical
  apply congrArg (fun c => (⟨i,j,c⟩ : Σ i, Σ j, Option ((source S).Atom i j)))
  change colour S x y = colour S z t
  apply Option.ext
  intro a
  cases a with
  | inl a => simp only [colour_old_iff,hc]
  | inr e =>
    rcases e with ⟨e⟩
    subst j
    exact (congrArg (fun c => c = some (.inr ⟨rfl⟩))
      (colour_ext S x y z t hc (by simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hd))).to_iff

/-- Diagonality is a Boolean observation of the complete typed atomic code. -/
theorem tagged_diagonal {p q r s : Sigma X}
    (h : taggedColour S p q = taggedColour S r s) : (p = q ↔ r = s) := by
  have hh := congrArg (fun z : Σ i, Σ j, Option (S.Atom i j) => z.2.2.isNone) h
  have hp : (S.colour p.2 q.2).isNone = true ↔ p = q := by
    rw [Option.isNone_iff_eq_none,S.colour_none_iff]
  have hr : (S.colour r.2 s.2).isNone = true ↔ r = s := by
    rw [Option.isNone_iff_eq_none,S.colour_none_iff]
  exact hp.symm.trans ((congrArg (fun b => b = true) hh).to_iff.trans hr)

/-- The owner image is an actual finite induced original substructure. -/
def ownerObject (A : FiniteInduced (X := Carrier X)) : FiniteInduced (X := X) where
  vertices := owner '' A.vertices
  finite_vertices := A.finite_vertices.image owner

noncomputable def ownerRep (A : FiniteInduced (X := Carrier X))
    (q : (ownerObject A).vertices) : A.vertices :=
  ⟨q.property.choose,q.property.choose_spec.1⟩

@[simp] theorem ownerRep_spec (A : FiniteInduced (X := Carrier X))
    (q : (ownerObject A).vertices) : owner (ownerRep A q).val = q.val :=
  q.property.choose_spec.2

/-- C02: every real induced clone embedding descends to an induced owner embedding. -/
noncomputable def ownerEmbedding {A B : FiniteInduced (X := Carrier X)}
    (e : InducedEmbedding (source S) A B) :
    InducedEmbedding S (ownerObject A) (ownerObject B) where
  toEmbedding := {
    toFun q := ⟨owner (e.toEmbedding (ownerRep A q)).val,
      ⟨(e.toEmbedding (ownerRep A q)).val,(e.toEmbedding (ownerRep A q)).property,rfl⟩⟩
    inj' := by
      intro q r he
      have hc := tagged_owner_eq S (e.preserves_colours (ownerRep A q) (ownerRep A r))
      have ht := (tagged_diagonal S hc).mpr (congrArg Subtype.val he)
      apply Subtype.ext
      simpa only [ownerRep_spec] using ht }
  preserves_sort := by
    intro q
    exact (e.preserves_sort (ownerRep A q)).trans (congrArg Sigma.fst (ownerRep_spec A q))
  preserves_colours := by
    intro q r
    change taggedColour S q.val r.val =
      taggedColour S (owner (e.toEmbedding (ownerRep A q)).val)
        (owner (e.toEmbedding (ownerRep A r)).val)
    have h := tagged_owner_eq S (e.preserves_colours (ownerRep A q) (ownerRep A r))
    simpa only [ownerRep_spec] using h

/-- Descent is independent of the chosen representative. -/
theorem ownerEmbedding_apply {A B : FiniteInduced (X := Carrier X)}
    (e : InducedEmbedding (source S) A B) (p : A.vertices) :
    ((ownerEmbedding S e).toEmbedding ⟨owner p.val,⟨p.val,p.property,rfl⟩⟩).val =
      owner (e.toEmbedding p).val := by
  let q : (ownerObject A).vertices := ⟨owner p.val,⟨p.val,p.property,rfl⟩⟩
  have he : owner (ownerRep A q).val = owner p.val := ownerRep_spec A q
  have hc := tagged_owner_eq S (e.preserves_colours (ownerRep A q) p)
  exact (tagged_diagonal S hc).mp he

end CCO.CloneSAP
