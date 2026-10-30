import CCO.CloneSAP.Owner
import CCO.CloneSAP.FiniteUnion
import Mathlib.Data.Fintype.EquivFin

universe u v w
namespace CCO.CloneSAP
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource ι X)

/-- Every finite owner assignment admits a globally injective pure-clone lift. -/
theorem fresh_lift {V : Type*} [Finite V] (f : V → Sigma X) :
    ∃ h : V ↪ Sigma (Carrier X), ∀ a, owner (h a) = f a := by
  classical
  letI := Fintype.ofFinite V
  let index : V ↪ ℕ := (Fintype.equivFin V).toEmbedding.trans ⟨Fin.val,Fin.val_injective⟩
  let h : V ↪ Sigma (Carrier X) := {
    toFun a := pointEquiv.symm (f a,index a)
    inj' := by
      intro a b he
      have hn := congrArg (fun p : Sigma (Carrier X) => p.2.2) he
      exact index.injective hn }
  refine ⟨h,?_⟩
  intro a
  exact congrArg Prod.fst (pointEquiv.apply_symm_apply (f a,index a))

/-- C11--C13: ordinary AP of owner diagrams suffices for real clone SAP.
No old strong amalgamation, homogeneity, CCO or triangle assumption is used. -/
theorem strong_amalgamation (ap : AgeAP S) : AgeSAP (source S) where
  strong_amalgamate := by
    classical
    intro C A B s t
    let os := ownerEmbedding S s
    let ot := ownerEmbedding S t
    obtain ⟨D,l,r,comm⟩ := ap.amalgamate (ownerObject C) (ownerObject A) (ownerObject B) os ot
    let oa (a : A.vertices) : D.vertices := l.toEmbedding ⟨owner a.val,⟨a.val,a.property,rfl⟩⟩
    let ob (b : B.vertices) : D.vertices := r.toEmbedding ⟨owner b.val,⟨b.val,b.property,rfl⟩⟩
    have ocomm (c : C.vertices) : oa (s.toEmbedding c) = ob (t.toEmbedding c) := by
      have he := comm ⟨owner c.val,⟨c.val,c.property,rfl⟩⟩
      have hs := ownerEmbedding_apply S s c
      have ht := ownerEmbedding_apply S t c
      have hs' : os.toEmbedding ⟨owner c.val,⟨c.val,c.property,rfl⟩⟩ =
          ⟨owner (s.toEmbedding c).val,⟨(s.toEmbedding c).val,(s.toEmbedding c).property,rfl⟩⟩ :=
        Subtype.ext hs
      have ht' : ot.toEmbedding ⟨owner c.val,⟨c.val,c.property,rfl⟩⟩ =
          ⟨owner (t.toEmbedding c).val,⟨(t.toEmbedding c).val,(t.toEmbedding c).property,rfl⟩⟩ :=
        Subtype.ext ht
      rw [hs',ht'] at he
      exact he
    let U := FiniteUnion.Union (A := A.vertices) t.toEmbedding
    letI : Finite A.vertices := A.finite_vertices.to_subtype
    letI : Finite B.vertices := B.finite_vertices.to_subtype
    letI : Finite C.vertices := C.finite_vertices.to_subtype
    letI : Fintype A.vertices := Fintype.ofFinite _
    letI : Fintype B.vertices := Fintype.ofFinite _
    letI : Fintype C.vertices := Fintype.ofFinite _
    letI : Finite U := by dsimp [U,FiniteUnion.Union,FiniteUnion.OffBase]; infer_instance
    let f : U → Sigma X := Sum.elim (fun a => (oa a).val) (fun b => (ob b.val).val)
    have fl (a : A.vertices) : f (FiniteUnion.left t.toEmbedding a) = (oa a).val := rfl
    have fr (b : B.vertices) : f (FiniteUnion.right s.toEmbedding t.toEmbedding b) = (ob b).val := by
      by_cases hb : b ∈ Set.range t.toEmbedding
      · obtain ⟨c,rfl⟩ := hb
        change f (FiniteUnion.rightFun s.toEmbedding t.toEmbedding (t.toEmbedding c)) = _
        rw [FiniteUnion.right_base]
        exact congrArg Subtype.val (ocomm c)
      · change f (FiniteUnion.rightFun s.toEmbedding t.toEmbedding b) = _
        rw [FiniteUnion.right_off _ _ b hb]
        rfl
    obtain ⟨h,hh⟩ := fresh_lift f
    let target : FiniteInduced (X := Carrier X) := {
      vertices := Set.range h
      finite_vertices := Set.finite_range h }
    let lift : U ↪ target.vertices := {
      toFun a := ⟨h a,⟨a,rfl⟩⟩
      inj' := fun _ _ he => h.injective (congrArg Subtype.val he) }
    let al : A.vertices ↪ target.vertices := (FiniteUnion.left t.toEmbedding).trans lift
    let bl : B.vertices ↪ target.vertices := (FiniteUnion.right s.toEmbedding t.toEmbedding).trans lift
    have oldl (a b : A.vertices) : taggedColour S (owner a.val) (owner b.val) =
        taggedColour S (owner (al a).val) (owner (al b).val) := by
      change taggedColour S (owner a.val) (owner b.val) =
        taggedColour S (owner (h (FiniteUnion.left t.toEmbedding a)))
          (owner (h (FiniteUnion.left t.toEmbedding b)))
      rw [hh,hh,fl,fl]
      exact l.preserves_colours ⟨owner a.val,⟨a.val,a.property,rfl⟩⟩ ⟨owner b.val,⟨b.val,b.property,rfl⟩⟩
    have oldr (a b : B.vertices) : taggedColour S (owner a.val) (owner b.val) =
        taggedColour S (owner (bl a).val) (owner (bl b).val) := by
      change taggedColour S (owner a.val) (owner b.val) =
        taggedColour S (owner (h (FiniteUnion.right s.toEmbedding t.toEmbedding a)))
          (owner (h (FiniteUnion.right s.toEmbedding t.toEmbedding b)))
      rw [hh,hh,fr,fr]
      exact r.preserves_colours ⟨owner a.val,⟨a.val,a.property,rfl⟩⟩ ⟨owner b.val,⟨b.val,b.property,rfl⟩⟩
    let ae : InducedEmbedding (source S) A target := {
      toEmbedding := al
      preserves_sort := by
        intro a
        have he := congrArg Sigma.fst (hh (FiniteUnion.left t.toEmbedding a))
        exact he.trans (l.preserves_sort _)
      preserves_colours := by
        intro a b
        exact tagged_reconstruct S (oldl a b) (by
          constructor
          · intro he; exact congrArg (fun x : A.vertices => (al x).val) (Subtype.ext he)
          · intro he; exact congrArg Subtype.val (al.injective (Subtype.ext he))) }
    let be : InducedEmbedding (source S) B target := {
      toEmbedding := bl
      preserves_sort := by
        intro b
        have he := congrArg Sigma.fst (hh (FiniteUnion.right s.toEmbedding t.toEmbedding b))
        rw [fr] at he
        exact he.trans (r.preserves_sort _)
      preserves_colours := by
        intro a b
        exact tagged_reconstruct S (oldr a b) (by
          constructor
          · intro he; exact congrArg (fun x : B.vertices => (bl x).val) (Subtype.ext he)
          · intro he; exact congrArg Subtype.val (bl.injective (Subtype.ext he))) }
    refine ⟨target,ae,be,?_,?_⟩
    · intro c
      exact congrArg lift (FiniteUnion.commute s.toEmbedding t.toEmbedding c)
    · intro a b he
      have hh' := lift.injective he
      exact FiniteUnion.intersection s.toEmbedding t.toEmbedding a b hh'

end CCO.CloneSAP
