import CCO.FullCode.CompositionCode

/-! Constructing the hidden embedding from the finite FULL code. -/
universe u v w a b
namespace CCO.FullCode.Object
variable {L : Language.{u}} {V : Type v} {W : Type w}
  {C : Structure L V} {D : Structure L W} {S : RootScheme L}
  {A : Type a} {B : Type b} {N : NormalForms L}
  {O : Object C S A} {P : Object D S B}

def Embedding.extensionGraph (f : Embedding N O P) (x : V) (y : W) : Prop :=
  ∃ a p, x ∈ (O.root a).presentation N p ∧ y ∈ (P.root (f.point a)).presentation N p

theorem Embedding.extensionGraph_exists (f : Embedding N O P) (hN : N.Valid C)
    (x : O.support) : ∃ y, f.extensionGraph x.val y := by
  obtain ⟨a, p, hx⟩ := (O.mem_support_iff_presentation N hN x.val).mp x.property
  have hsource : EqualityCode N (O.root a) (O.root a) p p := ⟨x.val, hx, hx⟩
  obtain ⟨y, hy, _⟩ := (f.equality_iff a a p p).mpr hsource
  exact ⟨y, a, p, hx, hy⟩

theorem Embedding.extensionGraph_functional (f : Embedding N O P) (x : V)
    {y z : W} (hy : f.extensionGraph x y) (hz : f.extensionGraph x z) : y = z := by
  obtain ⟨a, p, hxa, hy⟩ := hy
  obtain ⟨b, q, hxb, hz⟩ := hz
  obtain ⟨t, hta, htb⟩ := (f.equality_iff a b p q).mpr ⟨x, hxa, hxb⟩
  exact ((P.root (f.point a)).presentation_functional N p hy hta).trans
    ((P.root (f.point b)).presentation_functional N q htb hz)

noncomputable def Embedding.extendPoint (f : Embedding N O P) (hN : N.Valid C)
    (x : O.support) : W := Classical.choose (f.extensionGraph_exists hN x)

theorem Embedding.extendPoint_spec (f : Embedding N O P) (hN : N.Valid C)
    (x : O.support) : f.extensionGraph x.val (f.extendPoint hN x) :=
  Classical.choose_spec (f.extensionGraph_exists hN x)

theorem Embedding.extendPoint_presentation (f : Embedding N O P) (hN : N.Valid C)
    (x : O.support) (a : A) (p : Presentation N S)
    (hx : x.val ∈ (O.root a).presentation N p) :
    f.extendPoint hN x ∈ (P.root (f.point a)).presentation N p := by
  obtain ⟨b, q, hxb, hpoint⟩ := f.extendPoint_spec hN x
  obtain ⟨z, hza, hzb⟩ := (f.equality_iff a b p q).mpr ⟨x.val, hx, hxb⟩
  exact ((P.root (f.point b)).presentation_functional N q hzb hpoint) ▸ hza

theorem Embedding.extendPoint_injective (f : Embedding N O P) (hN : N.Valid C) :
    Function.Injective (f.extendPoint hN) := by
  intro x y hxy
  obtain ⟨a, p, hx⟩ := (O.mem_support_iff_presentation N hN x.val).mp x.property
  obtain ⟨b, q, hy⟩ := (O.mem_support_iff_presentation N hN y.val).mp y.property
  obtain ⟨z, hz, hzb⟩ := (f.equality_iff a b p q).mp
    ⟨f.extendPoint hN x, f.extendPoint_presentation hN x a p hx,
      hxy ▸ f.extendPoint_presentation hN y b q hy⟩
  apply Subtype.ext
  exact ((O.root a).presentation_functional N p hx hz).trans
    ((O.root b).presentation_functional N q hzb hy)

theorem Embedding.extendPoint_sort (f : Embedding N O P) (hN : N.Valid C)
    (x : O.support) : D.sort (f.extendPoint hN x) = C.sort x.val := by
  obtain ⟨a, p, hx⟩ := (O.mem_support_iff_presentation N hN x.val).mp x.property
  exact ((P.root (f.point a)).presentation_sorted N p
    (f.extendPoint_presentation hN x a p hx)).trans ((O.root a).presentation_sorted N p hx).symm

theorem Embedding.extendPoint_unary_iff (f : Embedding N O P) (hN : N.Valid C)
    (U : L.Unary) (x : O.support) :
    D.unary U (f.extendPoint hN x) ↔ C.unary U x.val := by
  obtain ⟨a, p, hx⟩ := (O.mem_support_iff_presentation N hN x.val).mp x.property
  have hpx := f.extendPoint_presentation hN x a p hx
  constructor
  · intro hU
    obtain ⟨z, hz, hUz⟩ := (f.unary_iff U a p).mp ⟨_, hpx, hU⟩
    exact ((O.root a).presentation_functional N p hz hx) ▸ hUz
  · intro hU
    obtain ⟨z, hz, hUz⟩ := (f.unary_iff U a p).mpr ⟨_, hx, hU⟩
    exact ((P.root (f.point a)).presentation_functional N p hz hpx) ▸ hUz

theorem Embedding.extendPoint_binary_iff (f : Embedding N O P) (hN : N.Valid C)
    (R : L.Binary) (x y : O.support) :
    D.binary R (f.extendPoint hN x) (f.extendPoint hN y) ↔ C.binary R x.val y.val := by
  obtain ⟨a, p, hx⟩ := (O.mem_support_iff_presentation N hN x.val).mp x.property
  obtain ⟨b, q, hy⟩ := (O.mem_support_iff_presentation N hN y.val).mp y.property
  have hpx := f.extendPoint_presentation hN x a p hx
  have hpy := f.extendPoint_presentation hN y b q hy
  constructor
  · intro hR
    obtain ⟨z, t, hz, ht, hRt⟩ := (f.binary_iff R a b p q).mp ⟨_, _, hpx, hpy, hR⟩
    have hzx := (O.root a).presentation_functional N p hz hx
    have hty := (O.root b).presentation_functional N q ht hy
    exact hzx ▸ hty ▸ hRt
  · intro hR
    obtain ⟨z, t, hz, ht, hRt⟩ := (f.binary_iff R a b p q).mpr ⟨_, _, hx, hy, hR⟩
    have hzx := (P.root (f.point a)).presentation_functional N p hz hpx
    have hty := (P.root (f.point b)).presentation_functional N q ht hpy
    exact hzx ▸ hty ▸ hRt

theorem Embedding.extendPoint_map_func (f : Embedding N O P) (hC : N.Valid C) (hD : N.Valid D)
    (F : L.Func) (x y : O.support) (hy : y.val ∈ C.func F x.val) :
    f.extendPoint hC y ∈ D.func F (f.extendPoint hC x) := by
  obtain ⟨a, p, hx⟩ := (O.mem_support_iff_presentation N hC x.val).mp x.property
  have ht : p.2.1 = L.input F := ((O.root a).presentation_sorted N p hx).symm.trans
    (C.func_sorted F x.val y.val hy).1
  have hpy : y.val ∈ (O.root a).presentation N (p.follow F ht) :=
    ((O.root a).presentation_follow N hC p F ht y.val).mpr ⟨x.val, hx, hy⟩
  have hfy := f.extendPoint_presentation hC y a (p.follow F ht) hpy
  obtain ⟨z, hz, hF⟩ := ((P.root (f.point a)).presentation_follow N hD p F ht _).mp hfy
  have hzx := (P.root (f.point a)).presentation_functional N p hz
    (f.extendPoint_presentation hC x a p hx)
  exact hzx ▸ hF

theorem Embedding.extendPoint_reflect_func (f : Embedding N O P) (hC : N.Valid C)
    (hD : N.Valid D) (F : L.Func) (x : O.support) (y : W)
    (hy : y ∈ D.func F (f.extendPoint hC x)) :
    ∃ z : O.support, z.val ∈ C.func F x.val ∧ f.extendPoint hC z = y := by
  obtain ⟨a, p, hx⟩ := (O.mem_support_iff_presentation N hC x.val).mp x.property
  have ht : p.2.1 = L.input F :=
    ((P.root (f.point a)).presentation_sorted N p (f.extendPoint_presentation hC x a p hx)).symm.trans
      (D.func_sorted F _ y hy).1
  have hyp : y ∈ (P.root (f.point a)).presentation N (p.follow F ht) :=
    ((P.root (f.point a)).presentation_follow N hD p F ht y).mpr
      ⟨_, f.extendPoint_presentation hC x a p hx, hy⟩
  obtain ⟨z, hz, _⟩ := (f.equality_iff a a (p.follow F ht) (p.follow F ht)).mp ⟨y, hyp, hyp⟩
  obtain ⟨t, ht', hF⟩ := ((O.root a).presentation_follow N hC p F ht z).mp hz
  have htx := (O.root a).presentation_functional N p ht' hx
  let z' : O.support := ⟨z, O.presentation_mem_support N a _ hz⟩
  refine ⟨z', htx ▸ hF, ?_⟩
  exact (P.root (f.point a)).presentation_functional N (p.follow F ht)
    (f.extendPoint_presentation hC z' a _ hz) hyp

noncomputable def Embedding.extend (f : Embedding N O P) (hC : N.Valid C) (hD : N.Valid D) :
    Structure.Embedding O.supportStructure D where
  point := f.extendPoint hC
  injective := f.extendPoint_injective hC
  sort_eq := f.extendPoint_sort hC
  map_func := f.extendPoint_map_func hC hD
  reflect_func := f.extendPoint_reflect_func hC hD
  unary_iff := f.extendPoint_unary_iff hC
  binary_iff := f.extendPoint_binary_iff hC

end CCO.FullCode.Object
