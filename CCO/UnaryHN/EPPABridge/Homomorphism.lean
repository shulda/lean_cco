import CCO.UnaryHN.EPPABridge.Irreducible
import CCO.UnaryHN.NativeTransferBasis

/-! The maps are genuine homomorphism-embeddings in both conventions.
Every closed irreducible is tested, including the empty one. -/

universe u v
namespace CCO.UnaryHN.Native.EPPABridge
open StructuralRamsey
open StructuralRamsey.Structure

def encodeHom {L : Language.{u}} {V W : Type v}
    {A : Structure L V} {B : Structure L W} {f : V → W}
    (hf : A.IsWeakHomomorphism B f) :
    AllThoseEPPA.Structure.Homomorphism (trivialAction L) (encode A) (encode B) where
  lang := PUnit.unit
  toFun := f
  map_rel := by
    intro n ⟨R, hR, hp⟩ xs hx
    subst n
    exact hf.1 R xs hx
  map_func := by
    intro n ⟨F, hF⟩ xs y hy
    subst n
    obtain ⟨z, hz, rfl⟩ := hy
    exact hf.2 F xs z hz

theorem encodeHE {L : Language.{u}} {V W : Type v}
    {A : Structure L V} {B : Structure L W} {f : V → W}
    (hf : HE A B f) :
    AllThoseEPPA.Structure.Homomorphism.IsHomomorphismEmbedding
      (trivialAction L) (encodeHom hf.1) := by
  intro S hS hIrr
  have hSN : A.IsClosed S := (encode_closed_iff A S).mp hS
  have hIN : (A.induce S hSN).Irreducible :=
    native_irreducible_of_encode _ (by simpa only [encode_induce] using hIrr)
  obtain ⟨g, hg⟩ := hf.2 _ hIN (A.inclusion S hSN)
  let ge := encodeEmbedding g
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have he : g ⟨x, hx⟩ = g ⟨y, hy⟩ := (hg ⟨x, hx⟩).trans (hxy.trans (hg ⟨y, hy⟩).symm)
    exact congrArg Subtype.val (g.injective he)
  · intro n R xs hxs
    let ys : Fin n → S := fun i => ⟨xs i, hxs i⟩
    have hargs : ge.toFun ∘ ys = f ∘ xs := funext fun i => hg (ys i)
    have hh := ge.map_rel_iff R ys
    rw [trivial_onRel (L := L), hargs] at hh
    exact hh
  · intro n F xs hxs
    let ys : Fin n → S := fun i => ⟨xs i, hxs i⟩
    have hargs : ge.toFun ∘ ys = f ∘ xs := funext fun i => hg (ys i)
    have hh := ge.map_func F ys
    rw [trivial_onFunc (L := L), hargs] at hh
    apply Eq.trans ?_ hh
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      have haS : a ∈ S := hS F xs hxs ha
      exact ⟨⟨a, haS⟩, ha, hg ⟨a, haS⟩⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.1, ha, (hg a).symm⟩

theorem decodeHE {L : Language.{u}} {V W : Type v}
    {A : Structure L V} {B : Structure L W} {P : NullaryProfile L}
    (hPA : HasProfile A P) (hPB : HasProfile B P)
    (f : AllThoseEPPA.Structure.Homomorphism (trivialAction L) (encode A) (encode B))
    (hf : AllThoseEPPA.Structure.Homomorphism.IsHomomorphismEmbedding (trivialAction L) f) :
    HE A B f.toFun := by
  constructor
  · constructor
    · intro R xs hx
      by_cases hp : 0 < L.relArity R
      · have hh := f.map_rel ⟨R, rfl, hp⟩ xs hx
        rw [trivial_onRel (L := L)] at hh
        exact hh
      · have hz := Nat.eq_zero_of_not_pos hp
        exact (hPB R hz (f.toFun ∘ xs)).mpr ((hPA R hz xs).mp hx)
    · intro F xs y hy
      have hh := f.map_func ⟨F, rfl⟩ xs ⟨y, hy, rfl⟩
      rw [trivial_onFunc (L := L)] at hh
      exact hh
  · intro X E hE e
    let ee := encodeEmbedding e
    have hES : (encode E).IsIrreducible := encode_irreducible_of_native E hE
    have hS : (encode A).IsClosed (Set.range ee.toFun) := ee.range_isClosed (trivialAction L)
    have hIS := ee.range_isIrreducible (trivialAction L) hES
    have hon := hf (Set.range ee.toFun) hS hIS
    refine ⟨{
      toFun := f.toFun ∘ e
      injective := by
        intro x y hxy
        apply e.injective
        exact hon.1 ⟨x, rfl⟩ ⟨y, rfl⟩ hxy
      map_rel_iff := by
        intro R xs
        by_cases hp : 0 < L.relArity R
        · have hh := hon.2.1 ⟨R, rfl, hp⟩ (e ∘ xs) (fun i => ⟨xs i, rfl⟩)
          rw [trivial_onRel (L := L)] at hh
          change B.rel R (f.toFun ∘ (e ∘ xs)) ↔ A.rel R (e ∘ xs) at hh
          exact hh.trans (e.map_rel_iff R xs)
        · have hz := Nat.eq_zero_of_not_pos hp
          exact (hPB R hz _).trans ((hPA R hz _).symm.trans (e.map_rel_iff R xs))
      map_func := by
        intro F xs
        have hh := hon.2.2 ⟨F, rfl⟩ (e ∘ xs) (fun i => ⟨xs i, rfl⟩)
        rw [trivial_onFunc (L := L)] at hh
        change AllThoseEPPA.Structure.imageSet f.toFun (A.func F (e ∘ xs)) = _ at hh
        rw [← e.map_func F xs] at hh
        change f.toFun '' (e.toFun '' E.func F xs) =
          B.func F (f.toFun ∘ (e ∘ xs)) at hh
        rw [Set.image_image] at hh
        exact hh }, fun _ => rfl⟩

def actualProfile {L : Language.{u}} {V : Type v} (A : Structure L V) : NullaryProfile L :=
  fun R _ => ∀ xs, A.rel R xs

theorem has_actualProfile {L : Language.{u}} {V : Type v} (A : Structure L V) :
    HasProfile A (actualProfile A) := by
  intro R h xs
  constructor
  · intro hx ys
    have he : xs = ys := by funext i; have := i.2; omega
    simpa [he] using hx
  · exact fun h => h xs

theorem HE_profile {L : Language.{u}} (hUnary : Unary L) {V W : Type v}
    {A : Structure L V} {B : Structure L W} {f : V → W} (hf : HE A B f) :
    HasProfile B (actualProfile A) := by
  have hEmpty : A.IsClosed ∅ := by
    intro F xs hxs
    let i : Fin (L.funcArity F) := ⟨0, by rw [hUnary F]; omega⟩
    exact False.elim (hxs i)
  have hIrr : (A.induce ∅ hEmpty).Irreducible := by
    intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hfree e
    left
    intro a
    exact False.elim a.2
  obtain ⟨g, _⟩ := hf.2 _ hIrr (A.inclusion ∅ hEmpty)
  apply embedding_profile g
  intro R h xs
  exact has_actualProfile A R h (Subtype.val ∘ xs)

end CCO.UnaryHN.Native.EPPABridge
