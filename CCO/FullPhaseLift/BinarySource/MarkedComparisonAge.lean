import CCO.FullPhaseLift.BinarySource.MarkedComparisonNames
import CCO.FullPhaseLift.BinarySource.FullReduct
import CCO.PairSafeSplit.Strong.Realization

/-! Exact actual finite pair-age comparison between the FULL marked limit
and the B047 pair source. All old pair codes and literal bits are retained;
the full finite age is used only to produce genuine marked pair witnesses. -/

universe m t
namespace CCO.FullPhaseLift.BinarySource.MarkedComparison
open Canonical APCharacter OwnerTransversal.CountableColour RigidGroupoid.Geometry
open APCharacter.SourceAge.UnarySource
noncomputable section
variable {L : Signature} {M : Type m} (U : BoolTable L M) (hsym : SameSortSymmetric U)
variable {G : Type t} [Group G] [∀ i, MulAction G (Canonical.Carrier U i)]
variable {H : HomogeneousSource (Canonical.source U hsym) G}
variable {C : ExactCalculus (Canonical.source U hsym)} {a : UnaryName U}
variable {K : RigidGroupoid.Geometry.Kernel (Canonical.source U hsym) a}
variable (P : SourcePhase (Canonical.source U hsym) H C K)
variable (cco : SemanticCCO.{0,m,m,0} (Canonical.source U hsym))
variable (I : Identification (Canonical.source U hsym) H (P.completion_property cco))

def targetOld : NewPoint I ≃ M := (oldEquiv I).trans (Canonical.pack U).symm
def targetBits (p : NewPoint I) : Bit := (childLabel I p.1).2
def targetTable := codeTable (pullback U (targetOld U hsym P cco I)) (targetBits U hsym P cco I)

theorem pack_targetOld (p : NewPoint I) :
    Canonical.pack U (targetOld U hsym P cco I p) = oldEquiv I p :=
  (Canonical.pack U).apply_symm_apply _

theorem target_owner (p : NewPoint I) :
    (targetTable U hsym P cco I).owner p = ((childLabel I p.1).1.val,(childLabel I p.1).2) := by
  apply Prod.ext
  · exact congrArg (fun q : Sigma (Canonical.Carrier U) => q.1.val)
      (pack_targetOld U hsym P cco I p)
  · rfl

theorem target_colour (p q : NewPoint I) :
    (targetTable U hsym P cco I).colour p q =
      tagCode U (taggedColour (Canonical.source U hsym) (oldEquiv I p) (oldEquiv I q)) := by
  let e : Canonical.Embedding (pullback U (targetOld U hsym P cco I)) U :=
    embeddingOf (targetOld U hsym P cco I) (targetOld U hsym P cco I).injective (fun _ _ => rfl)
  change pairNameCode (pullback U (targetOld U hsym P cco I)) p q = _
  calc
    _ = pairNameCode U (targetOld U hsym P cco I p) (targetOld U hsym P cco I q) :=
      (pairNameCode_embedding e p q).symm
    _ = tagCode U (taggedColour (Canonical.source U hsym)
      (Canonical.pack U (targetOld U hsym P cco I p))
      (Canonical.pack U (targetOld U hsym P cco I q))) :=
      (tagCode_pack_eq_pairNameCode U hsym _ _).symm
    _ = _ := by rw [pack_targetOld,pack_targetOld]

theorem mark_targetBits (p : NewPoint I) :
    mark I (oldEquiv I p) = targetBits U hsym P cco I p := by
  rcases p with ⟨c,x⟩
  exact congrArg Subtype.val x.property

variable (sap : Marked.StrongAmalgamation U (Canonical.source U hsym) (Canonical.pack U) P.masks)

abbrev Model := FullReduct.Carrier U (Canonical.source U hsym) (Canonical.pack U) P.masks sap
def modelTable := codeTable
  (FullReduct.oldTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap)
  (FullReduct.bits U (Canonical.source U hsym) (Canonical.pack U) P.masks sap)

theorem model_to_target_age : AgeMaps (modelTable U hsym P sap) (targetTable U hsym P cco I) := by
  intro n p
  obtain ⟨r,hr⟩ := FullReduct.finite_old_witness U (Canonical.source U hsym)
    (Canonical.pack U) P.masks sap p
  let point : Fin n → Sigma (Canonical.Carrier U) := Canonical.pack U ∘ r.point
  let bits := FullReduct.bits U (Canonical.source U hsym) (Canonical.pack U) P.masks sap ∘ p
  obtain ⟨f,ho,hc⟩ := PairSafeSplit.Strong.Realization.embed_legal_tuple P cco I point bits hr
  have hi : Function.Injective f := PairSafeSplit.Strong.Realization.injective_of_old_names P cco I
    point f hc ((Canonical.pack U).injective.comp r.injective)
  let q : Fin n ↪ NewPoint I := ⟨f,hi⟩
  let oldp : Canonical.Embedding
      (pullback (FullReduct.oldTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap) p)
      (FullReduct.oldTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap) :=
    embeddingOf p p.injective (fun _ _ => rfl)
  refine ⟨q,?_,?_⟩
  · intro x
    rw [target_owner]
    have h := ho x
    change ((childLabel I (f x).1).1.val,(childLabel I (f x).1).2) =
      (unaryProfile (FullReduct.oldTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap) (p x),bits x)
    apply Prod.ext
    · have hs := congrArg (fun s => s.1.val) h
      exact hs.trans (unaryProfile_embedding r x)
    · exact congrArg (fun s : UnaryName U × Bit => s.2) h
  · intro x y
    rw [target_colour]
    have h := congrArg (tagCode U) (hc x y)
    change tagCode U (taggedColour (Canonical.source U hsym) (oldEquiv I (f x)) (oldEquiv I (f y))) =
      tagCode U (taggedColour (Canonical.source U hsym) (Canonical.pack U (r.point x))
        (Canonical.pack U (r.point y))) at h
    rw [tagCode_pack_eq_pairNameCode] at h
    exact h.trans ((pairNameCode_embedding r x y).trans (pairNameCode_embedding oldp x y).symm)

theorem target_to_model_age : AgeMaps (targetTable U hsym P cco I) (modelTable U hsym P sap) := by
  intro n p
  let old : Fin n ↪ M := p.trans (targetOld U hsym P cco I).toEmbedding
  let T := pullback U old
  let b : Fin n → Bit := targetBits U hsym P cco I ∘ p
  let r : Canonical.Embedding T U := embeddingOf old old.injective (fun _ _ => rfl)
  let targetEmbedding : Canonical.Embedding T (pullback U (targetOld U hsym P cco I)) :=
    embeddingOf p p.injective (fun _ _ => rfl)
  have hpoint (x : Fin n) : Canonical.pack U (r.point x) = oldEquiv I (p x) := by
    change Canonical.pack U (targetOld U hsym P cco I (p x)) = _
    exact pack_targetOld U hsym P cco I (p x)
  have hmark (x : Fin n) : mark I (oldEquiv I (p x)) = b x :=
    mark_targetBits U hsym P cco I (p x)
  have legal : Age.Legal (Canonical.source U hsym) P.masks (Canonical.pack U ∘ r.point) b := by
    constructor
    · intro x
      change P.masks.validBit (Canonical.pack U (r.point x)).1 (b x)
      rw [hpoint,← hmark]
      exact (global_marking I).1 (oldEquiv I (p x))
    · intro x y
      change P.masks.allowed ((Canonical.source U hsym).colour (Canonical.pack U (r.point x)).2
        (Canonical.pack U (r.point y)).2) (b x) (b y)
      rw [hpoint,hpoint,← hmark,← hmark]
      exact (global_marking I).2 (oldEquiv I (p x)) (oldEquiv I (p y))
  let D : Marked.Chart U (Canonical.source U hsym) (Canonical.pack U) P.masks :=
    ⟨⟨n,T,⟨r⟩⟩,b,⟨r,legal⟩⟩
  let e := (Marked.data U (Canonical.source U hsym) (Canonical.pack U) P.masks sap).chart_embeds D
  let f := FullReduct.fromLimit U (Canonical.source U hsym) (Canonical.pack U) P.masks sap e.some
  let q : Fin n ↪ Model U hsym P sap := ⟨f.point,f.injective⟩
  let oldf : Canonical.Embedding T
      (FullReduct.oldTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap) :=
    embeddingOf f.point f.injective (fun r xs => embedding_read f r.succ xs)
  have hb (x : Fin n) :
      FullReduct.bits U (Canonical.source U hsym) (Canonical.pack U) P.masks sap (f.point x) = b x := by
    have h := embedding_read f 0 (fun _ => x)
    have hh := congrArg Marked.boolBit h
    change FullReduct.bits U (Canonical.source U hsym) (Canonical.pack U) P.masks sap (f.point x) =
      Marked.boolBit (Marked.bitBool (b x)) at hh
    exact hh.trans (Marked.boolBit_bitBool _)
  refine ⟨q,?_,?_⟩
  · intro x
    apply Prod.ext
    · exact (unaryProfile_embedding oldf x).trans (unaryProfile_embedding targetEmbedding x).symm
    · exact hb x
  · intro x y
    exact (pairNameCode_embedding oldf x y).trans (pairNameCode_embedding targetEmbedding x y).symm

end
end CCO.FullPhaseLift.BinarySource.MarkedComparison
