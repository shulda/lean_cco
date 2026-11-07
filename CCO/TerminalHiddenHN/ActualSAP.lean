import CCO.TerminalHiddenHN.CompletionBridge
import CCO.HiddenSAPReadings.SourceExports

/-! Whole actual closed-age SAP on arbitrary finite carrier presentations.
Every map is transported through its full closed induced image. The final
finite amalgam is reindexed into the caller's carrier universe. -/

universe u v w r z q
namespace CCO.TerminalHiddenHN
open CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.HiddenSAPReadings
noncomputable section

namespace ClosedAgeTransport
variable {L : CCO.UnaryFreshFrames.Language.{u}}
variable [Finite L.Sorts] [Finite L.Func] [Finite L.Rel]
variable {Ω : Type v} (B : CCO.UnaryFreshFrames.Structure L Ω)

abbrev Model (A : B.Piece) : Structure (partialSignature L) A.points :=
  (partialTarget B).induce A.points ((partialTarget_closed_iff B A.points).mpr A.closed)

theorem model_func_iff (A : B.Piece) (F : L.Func) (x y : A.points) :
    y ∈ (Model B A).func F x ↔ B.sort x.val = L.input F ∧ y.val = B.func F x.val := by
  classical
  change y.val ∈ (if B.sort x.val = L.input F then ({B.func F x.val} : Set Ω) else ∅) ↔ _
  by_cases h : B.sort x.val = L.input F <;> simp [h]

def image {V : Type z} [Finite V] {C : Structure (partialSignature L) V}
    (e : C.Embedding (partialTarget B)) : B.Piece :=
  ⟨Set.range e.point,Set.finite_range _,
    (partialTarget_closed_iff B _).mp (SourceSupport.embedding_range_closed e)⟩

def imageIso {V : Type z} [Finite V] {C : Structure (partialSignature L) V}
    (e : C.Embedding (partialTarget B)) : DiagramIso C (Model B (image B e)) :=
  SourceSupport.embedding_image_iso e

/-- The SAME complete piece map, with genuine on-sort partial graphs. -/
def partialEmbedding {A D : B.Piece} (e : A.Embedding D.points) :
    (Model B A).Embedding (Model B D) where
  point x := ⟨e.point x,e.mem_point x⟩
  sort_eq := e.sort_eq
  injective x y h := e.injective (congrArg Subtype.val h)
  map_func F x y hy := by
    obtain ⟨hs,hy⟩ := (model_func_iff B A F x y).mp hy
    apply (model_func_iff B D F _ _).mpr
    refine ⟨(e.sort_eq x).trans hs,?_⟩
    have he : y = A.func F x := Subtype.ext hy
    exact (congrArg e.point he).trans (e.func_eq F x)
  reflect_func F x y hy := by
    obtain ⟨hs,hy⟩ := (model_func_iff B D F _ _).mp hy
    have hx : B.sort x.val = L.input F := (e.sort_eq x).symm.trans hs
    refine ⟨A.func F x,(model_func_iff B A F x _).mpr ⟨hx,rfl⟩,?_⟩
    apply Subtype.ext
    exact (e.func_eq F x).trans hy.symm
  map_rel R xs := (e.rel_iff R xs).mpr
  reflect_rel R xs := (e.rel_iff R xs).mp

/-- Domain reflection recovers the canonical off-sort identity too;
it never adds an off-sort displayed edge to the partial source. -/
def completeEmbedding {A D : B.Piece} (e : (Model B A).Embedding (Model B D)) :
    A.Embedding D.points where
  point x := (e.point x).val
  mem_point x := (e.point x).property
  injective x y h := e.injective (Subtype.ext h)
  sort_eq := e.sort_eq
  func_eq F x := by
    by_cases hs : B.sort x.val = L.input F
    · have he := e.map_func F x (A.func F x)
        ((model_func_iff B A F x _).mpr ⟨hs,rfl⟩)
      exact ((model_func_iff B D F _ _).mp he).2
    · have hi : B.sort (e.point x).val ≠ L.input F := by
        intro h
        exact hs ((e.sort_eq x).symm.trans h)
      have hx : A.func F x = x := Subtype.ext (B.func_offsort F x.val hs)
      rw [hx,B.func_offsort F (e.point x).val hi]
  rel_iff R xs := ⟨e.reflect_rel R xs,e.map_rel R xs⟩

def Age {V : Type z} (C : Structure (partialSignature L) V) : Prop :=
  Finite V ∧ Nonempty (C.Embedding (partialTarget B))

/-- Generic receiving bridge from actual-subset SAP to the full
carrier-polymorphic class. The concrete source supplies subset SAP below. -/
theorem finiteHereditarySAP (hSAP : B.AgeSAP) :
    CCO.UnaryHN.Raw.FiniteHereditarySAP (Age.{u,v,z} B) where
  finite _ h := h.1
  hereditary := by
    intro V W C D hD e
    letI : Finite W := hD.1
    obtain ⟨f⟩ := hD.2
    exact ⟨Finite.of_injective e.point e.injective,⟨embedding_comp e f⟩⟩
  strong := by
    intro U V W Root Left Right hL hR sL sR
    letI : Finite V := hL.1
    letI : Finite W := hR.1
    letI : Finite U := Finite.of_injective sL.point sL.injective
    obtain ⟨fL⟩ := hL.2
    obtain ⟨fR⟩ := hR.2
    let fA := embedding_comp sL fL
    let A := image B fA
    let D := image B fL
    let E := image B fR
    let iA := imageIso B fA
    let iD := imageIso B fL
    let iE := imageIso B fR
    let aD := embedding_comp (diagramIso_symm iA).toEmbedding
      (embedding_comp sL iD.toEmbedding)
    let aE := embedding_comp (diagramIso_symm iA).toEmbedding
      (embedding_comp sR iE.toEmbedding)
    let s := completeEmbedding B aD
    let t := completeEmbedding B aE
    obtain ⟨F,l,r,hComm,hInt⟩ := hSAP A D E s t
    let jL := embedding_comp iD.toEmbedding (partialEmbedding B l)
    let jR := embedding_comp iE.toEmbedding (partialEmbedding B r)
    have comm (h : U) : jL.point (sL.point h) = jR.point (sR.point h) := by
      apply Subtype.ext
      change l.point (iD.equiv (sL.point h)) = r.point (iE.equiv (sR.point h))
      have hh := hComm (iA.equiv h)
      change l.point (iD.equiv (sL.point (iA.equiv.symm (iA.equiv h)))) =
        r.point (iE.equiv (sR.point (iA.equiv.symm (iA.equiv h)))) at hh
      simpa only [Equiv.symm_apply_apply] using hh
    have inter (x : V) (y : W) (he : jL.point x = jR.point y) :
        ∃ h : U, x = sL.point h ∧ y = sR.point h := by
      have hv : l.point (iD.equiv x) = r.point (iE.equiv y) := congrArg Subtype.val he
      obtain ⟨a,haD,haE⟩ := hInt (iD.equiv x) (iE.equiv y) hv
      refine ⟨iA.equiv.symm a,?_,?_⟩
      · have hh : fL.point (sL.point (iA.equiv.symm a)) = fL.point x := haD
        exact (fL.injective hh).symm
      · have hh : fR.point (sR.point (iA.equiv.symm a)) = fR.point y := haE
        exact (fR.injective hh).symm
    letI : Fintype F.points := Fintype.ofFinite F.points
    let Q := ULift.{z} (Fin (Fintype.card F.points))
    let e : Q ≃ F.points := Equiv.ulift.trans (Fintype.equivFin F.points).symm
    let T := pullbackStructure (Model B F) e
    let iso := pullbackStructureIso (Model B F) e
    let jL' := embedding_comp jL (diagramIso_symm iso).toEmbedding
    let jR' := embedding_comp jR (diagramIso_symm iso).toEmbedding
    have hT : Age B T := ⟨inferInstance,⟨embedding_comp iso.toEmbedding
      ((partialTarget B).inclusion F.points
        ((partialTarget_closed_iff B F.points).mpr F.closed))⟩⟩
    refine ⟨Q,inferInstance,T,hT,jL',jR',?_,?_⟩
    · intro h
      change e.symm (jL.point (sL.point h)) = e.symm (jR.point (sR.point h))
      exact congrArg e.symm (comm h)
    · intro x y he
      have hh : jL.point x = jR.point y := e.symm.injective he
      exact inter x y hh

end ClosedAgeTransport

open CCO.TypedOrbitFrames
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))

/-- C30 for the ENTIRE actual finite closed age, with arbitrary carrier
presentations, empty/orphan bases and the exact strong intersection. -/
theorem actualAge_finiteHereditarySAP [∀ i, Countable (X i)]
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    CCO.UnaryHN.Raw.FiniteHereditarySAP (ActualAge.{u,v,w,r,z} S H sap hCover) := by
  have hSAP := (CCO.HiddenSAPReadings.Source.typed_hidden_sap S H sap hCover cco).2.2
  exact ClosedAgeTransport.finiteHereditarySAP (Hidden S H sap hCover) hSAP

theorem actual_hidden_age_sap [∀ i, Countable (X i)]
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    CCO.UnaryHN.Raw.FiniteHereditarySAP (ActualAge.{u,v,w,r,z} S H sap hCover) :=
  actualAge_finiteHereditarySAP S H sap hCover cco

/-- JEP over the empty base, for the SAME whole actual age. In
particular neither object needs to be generated by internal real roots. -/
theorem actual_hidden_age_jep [∀ i, Countable (X i)]
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {V W : Type z}
    {A : Structure (Sig S H sap hCover) V}
    {B : Structure (Sig S H sap hCover) W}
    (hA : ActualAge S H sap hCover A) (hB : ActualAge S H sap hCover B) :
    ∃ (Q : Type z) (_ : Finite Q) (D : Structure (Sig S H sap hCover) Q),
      ActualAge S H sap hCover D ∧ Nonempty (A.Embedding D) ∧ Nonempty (B.Embedding D) := by
  let Root := A.induce ∅ A.isClosed_empty
  let s : Root.Embedding A := A.inclusion ∅ A.isClosed_empty
  let t : Root.Embedding B := {
    point := fun x => False.elim x.property
    sort_eq := fun x => False.elim x.property
    map_func := fun _ x _ _ => False.elim x.property
    map_rel := by
      intro R xs _
      exact False.elim (xs ⟨0,by rw [sig_binary S H sap hCover R]; decide⟩).property
    injective := fun x _ _ => False.elim x.property
    reflect_func := fun _ x _ _ => False.elim x.property
    reflect_rel := by
      intro R xs _
      exact False.elim (xs ⟨0,by rw [sig_binary S H sap hCover R]; decide⟩).property }
  obtain ⟨Q,hQ,D,hD,l,r,_,_⟩ :=
    (actualAge_finiteHereditarySAP S H sap hCover cco).strong hA hB s t
  exact ⟨Q,hQ,D,hD,⟨l⟩,⟨r⟩⟩

end
end CCO.TerminalHiddenHN
