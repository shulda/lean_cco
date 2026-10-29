import CCO.HKNReservoir.SourceAutomorphisms
import CCO.HKNReservoir.ClosedSpan
import CCO.HKNReservoir.StrongTree

universe u v w t x y
namespace CCO.HKNReservoir
noncomputable section
open AllThoseEPPA

/-- An exact embedding factors through any closed subset containing its
WHOLE image, retaining its one global language component. -/
def embeddingIntoInduce {L : Language.{u}} {Γ : Type t} [Group Γ]
    (act : L.Action Γ) {X : Type x} {Y : Type y}
    {A : Structure L X} {D : Structure L Y} (f : Structure.Embedding act A D)
    (P : Set Y) (hP : D.IsClosed P) (hf : Set.range f.toFun ⊆ P) :
    Structure.Embedding act A (D.induce P hP) where
  lang := f.lang
  toFun z := ⟨f z,hf ⟨z,rfl⟩⟩
  injective := fun _ _ h => f.injective (congrArg Subtype.val h)
  map_rel_iff := fun R xs => f.map_rel_iff R xs
  map_func := by
    intro n F xs
    ext z
    constructor
    · rintro ⟨a,ha,haz⟩
      change z.val ∈ D.func (act.onFunc f.lang F) (f.toFun ∘ xs)
      have hh : f a ∈ Structure.imageSet f.toFun (A.func F xs) := ⟨a,ha,rfl⟩
      rw [f.map_func] at hh
      exact (congrArg Subtype.val haz) ▸ hh
    · intro hz
      change z.val ∈ D.func (act.onFunc f.lang F) (f.toFun ∘ xs) at hz
      rw [← f.map_func] at hz
      obtain ⟨a,ha,he⟩ := hz
      exact ⟨a,ha,Subtype.ext he⟩

 theorem embedding_ext {L : Language.{u}} {Γ : Type t} [Group Γ]
    {act : L.Action Γ} {X : Type x} {Y : Type y}
    {A : Structure L X} {D : Structure L Y} (f g : Structure.Embedding act A D)
    (hl : f.lang = g.lang) (hv : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk fl ff fi fr fc =>
    cases g with
    | mk gl gf gi gr gc =>
      dsimp only at hl hv
      cases hl
      have he : ff = gf := funext hv
      cases he
      rfl

open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))

/-- Literal finite image in the named source; no selected origin is used. -/
def namedRange {X : Type x} [Finite X] (f : X → SourceCarrier S H R B) :
    Finset (NamedCarrier S H R B) := (Set.finite_range (fun x => (f x).down)).toFinset

@[simp] theorem mem_namedRange {X : Type x} [Finite X]
    (f : X → SourceCarrier S H R B) (z : NamedCarrier S H R B) :
    z ∈ namedRange S H R B f ↔ ∃ x, (f x).down = z := by
  simp [namedRange]

/-- WHOLE function-fibre equality of a genuine embedding makes its finite
image packet-closed, even when its domain has arbitrary set-valued functions. -/
theorem namedRange_closed {X : Type x} [Finite X]
    {A : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) X}
    (f : Structure.Embedding (sourceAction S H R B Δ) A (sourceStructure S H R B hB)) :
    PacketClosed S H R B (namedRange S H R B f.toFun) := by
  intro a ha b hab
  obtain ⟨x,rfl⟩ := (mem_namedRange S H R B f.toFun a).mp ha
  obtain ⟨g,hg⟩ := (packetPoint_range S H R B hB (f x).down ▸ hab :
    b ∈ Set.range (fun g => packetPoint S H R B hB g (f x).down))
  have hh : ULift.up b ∈ Structure.imageSet f.toFun (A.func (.translate g) (fun _ => x)) := by
    have he := f.map_func (.translate g) (fun _ => x)
    rw [he]
    change ULift.up b ∈ {ULift.up (packetPoint S H R B hB g (f x).down)}
    exact congrArg ULift.up hg.symm
  obtain ⟨y,_,hy⟩ := hh
  exact (mem_namedRange S H R B f.toFun b).mpr ⟨y,congrArg ULift.down hy⟩

theorem packetClosed_isClosed (P : Finset (NamedCarrier S H R B))
    (hP : PacketClosed S H R B P) :
    (sourceStructure S H R B hB).IsClosed {x | x.down ∈ P} := by
  apply (isClosed_encode_iff (sourceData S H R B hB) _).mpr
  intro g x hx
  exact hP x.down hx _ (translation_in_packet S (finitePacket S H) G g x.down.val)

/-- The target fine atoms are fixed by every global component. -/
theorem target_fine_iff {X : Type x}
    {A : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) X}
    (f : Structure.Embedding (sourceAction S H R B Δ) A (sourceStructure S H R B hB))
    (a : S.Atom () ()) (p q : X) :
    col S (f p).down.val (f q).down.val = some a ↔ A.rel (.fine a) (![p,q]) := by
  have hh := f.map_rel_iff (.fine a) (![p,q])
  simpa only [sourceAction,action_fine,sourceStructure,encode_fine,sourceData,
    Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.cons_val_fin_one] using hh

theorem equal_embedding_colours {X : Type x}
    {A : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) X}
    (f g : Structure.Embedding (sourceAction S H R B Δ) A (sourceStructure S H R B hB))
    (p q : X) : col S (f p).down.val (f q).down.val = col S (g p).down.val (g q).down.val := by
  have hh (a) := (target_fine_iff S H R B hB Δ f a p q).trans
    (target_fine_iff S H R B hB Δ g a p q).symm
  cases hf : col S (f p).down.val (f q).down.val with
  | none =>
    cases hg : col S (g p).down.val (g q).down.val with
    | none => rfl
    | some a => have hc := (hh a).mpr hg; rw [hf] at hc; cases hc
  | some a => exact ((hh a).mp hf).symm

theorem equal_embedding_owners {X : Type x}
    {A : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) X}
    (f g : Structure.Embedding (sourceAction S H R B Δ) A (sourceStructure S H R B hB))
    (hl : f.lang = g.lang) (p : X) : owner S H R (f p).down.val = owner S H R (g p).down.val := by
  let b := (sourceTag S H R B Δ f.lang).symm (ownerLabel S H R B (f p).down)
  have hf := f.map_rel_iff (.owner b) (fun _ => p)
  have hg := g.map_rel_iff (.owner b) (fun _ => p)
  have hrel : A.rel (.owner b) (fun _ => p) := hf.mp (by
    change ownerLabel S H R B (f p).down = sourceTag S H R B Δ f.lang b
    exact ((sourceTag S H R B Δ f.lang).apply_symm_apply _).symm)
  have he := hg.mpr hrel
  change ownerLabel S H R B (g p).down = sourceTag S H R B Δ g.lang b at he
  rw [← hl] at he
  have he' : ownerLabel S H R B (g p).down = ownerLabel S H R B (f p).down := by simpa only [b,Equiv.apply_symm_apply] using he
  exact congrArg Subtype.val he'.symm

/-- Two genuine embeddings of the same complete closed interface, with
one common global component, induce an actual named embedding of images. -/
def rangeCorrespondence {X : Type x} [Finite X]
    {A : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) X}
    (f g : Structure.Embedding (sourceAction S H R B Δ) A (sourceStructure S H R B hB))
    (hl : f.lang = g.lang) (P : Finset (NamedCarrier S H R B))
    (hP : ∀ x, (g x).down ∈ P) :
    NamedEmbedding S H R B (namedRange S H R B f.toFun) P := by
  classical
  let rep (c : ↥(namedRange S H R B f.toFun)) : X :=
    Classical.choose ((mem_namedRange S H R B f.toFun c.val).mp c.property)
  have hr (c : ↥(namedRange S H R B f.toFun)) : (f (rep c)).down = c.val :=
    Classical.choose_spec ((mem_namedRange S H R B f.toFun c.val).mp c.property)
  refine ⟨⟨fun c => ⟨(g (rep c)).down,hP _⟩,?_⟩,?_,?_⟩
  · intro c d he
    have hrep : rep c = rep d := g.injective (ULift.ext _ _ (congrArg Subtype.val he))
    exact Subtype.ext ((hr c).symm.trans ((congrArg (fun x => (f x).down) hrep).trans (hr d)))
  · intro c
    change owner S H R (g (rep c)).down.val = owner S H R c.val.val
    rw [← hr c]
    exact (equal_embedding_owners S H R B hB Δ f g hl (rep c)).symm
  · intro c d
    change col S (g (rep c)).down.val (g (rep d)).down.val = col S c.val.val d.val.val
    rw [← hr c,← hr d]
    exact (equal_embedding_colours S H R B hB Δ f g (rep c) (rep d)).symm

theorem rangeCorrespondence_apply {X : Type x} [Finite X]
    {A : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) X}
    (f g : Structure.Embedding (sourceAction S H R B Δ) A (sourceStructure S H R B hB))
    (hl : f.lang = g.lang) (P : Finset (NamedCarrier S H R B))
    (hP : ∀ x, (g x).down ∈ P) (x : X) :
    ((rangeCorrespondence S H R B hB Δ f g hl P hP).toEmbedding
      ⟨(f x).down,(mem_namedRange S H R B f.toFun _).mpr ⟨x,rfl⟩⟩).val = (g x).down := by
  classical
  change (g (Classical.choose ((mem_namedRange S H R B f.toFun (f x).down).mp
    ((mem_namedRange S H R B f.toFun (f x).down).mpr ⟨x,rfl⟩)))).down = (g x).down
  apply congrArg (fun z => (g z).down)
  apply f.injective
  apply ULift.ext
  exact Classical.choose_spec ((mem_namedRange S H R B f.toFun (f x).down).mp
    ((mem_namedRange S H R B f.toFun (f x).down).mpr ⟨x,rfl⟩))

end
end CCO.HKNReservoir
