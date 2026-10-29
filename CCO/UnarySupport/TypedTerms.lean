import CCO.UnarySupport.HNDiagrams

/-! Type-correct unary terms in ONE variable. Evaluation uses only actual
partial-function values; induced embeddings reflect the entire evaluation. -/

universe u v w
namespace CCO.UnarySupport.Structure
variable {L : Signature.{u}} {V : Type v} {W : Type w}

inductive Term (L : Signature.{u}) : L.Sorts → L.Sorts → Type u
  | var (i : L.Sorts) : Term L i i
  | func {i : L.Sorts} (F : L.Func) (t : Term L i (L.input F)) : Term L i (L.output F)

def eval (C : Structure L V) {i j : L.Sorts} : Term L i j → V → Set V
  | .var _, x => {x}
  | .func F t, x => {y | ∃ z, z ∈ eval C t x ∧ y ∈ C.func F z}

@[simp] theorem eval_var (C : Structure L V) (i : L.Sorts) (x : V) :
    C.eval (.var i) x = {x} := rfl

@[simp] theorem eval_func (C : Structure L V) {i : L.Sorts}
    (F : L.Func) (t : Term L i (L.input F)) (x y : V) :
    y ∈ C.eval (.func F t) x ↔ ∃ z, z ∈ C.eval t x ∧ y ∈ C.func F z := Iff.rfl

theorem eval_functional (C : Structure L V) {i j : L.Sorts} (t : Term L i j)
    {x y z : V} : y ∈ C.eval t x → z ∈ C.eval t x → y = z := by
  induction t generalizing y z with
  | var => exact fun hy hz => hy.trans hz.symm
  | func F t ih =>
    rintro ⟨a,ha,hay⟩ ⟨b,hb,hbz⟩
    have hab := ih ha hb
    subst b
    exact C.functional F a y z hay hbz

theorem eval_sorted (C : Structure L V) {i j : L.Sorts} (t : Term L i j)
    {x y : V} (hx : C.sort x = i) (hy : y ∈ C.eval t x) : C.sort y = j := by
  cases t with
  | var => exact hy ▸ hx
  | func F t => obtain ⟨z,_,hz⟩ := hy; exact (C.func_sorted F z y hz).2

theorem eval_nonempty (C : Structure L V) (hC : C.Total)
    {i j : L.Sorts} (t : Term L i j) {x : V} (hx : C.sort x = i) :
    (C.eval t x).Nonempty := by
  induction t with
  | var => exact ⟨x,rfl⟩
  | func F t ih =>
    obtain ⟨y,hy⟩ := ih
    obtain ⟨z,hz⟩ := hC F y (C.eval_sorted t hx hy)
    exact ⟨z,y,hy,hz⟩

theorem eval_closed (C : Structure L V) {S : Set V} (hS : C.IsClosed S)
    {i j : L.Sorts} (t : Term L i j) {x : V} (hx : x ∈ S) : C.eval t x ⊆ S := by
  induction t with
  | var => exact fun _ hy => hy ▸ hx
  | func F t ih =>
    rintro y ⟨z,hz,hzy⟩
    exact hS F z (ih hz) hzy

theorem Hom.map_eval {C : Structure L V} {D : Structure L W} (f : Hom C D)
    {i j : L.Sorts} (t : Term L i j) {x y : V} (hy : y ∈ C.eval t x) :
    f.point y ∈ D.eval t (f.point x) := by
  induction t generalizing y with
  | var => exact congrArg f.point hy
  | func F t ih =>
    obtain ⟨z,hz,hzy⟩ := hy
    exact ⟨f.point z,ih hz,f.map_func F z y hzy⟩

theorem Embedding.reflect_eval {C : Structure L V} {D : Structure L W} (f : Embedding C D)
    {i j : L.Sorts} (t : Term L i j) {x : V} {z : W} (hz : z ∈ D.eval t (f.point x)) :
    ∃ y, y ∈ C.eval t x ∧ f.point y = z := by
  induction t generalizing z with
  | var => exact ⟨x,rfl,hz.symm⟩
  | func F t ih =>
    obtain ⟨a,ha,haz⟩ := hz
    obtain ⟨b,hb,rfl⟩ := ih ha
    obtain ⟨y,hy,hfy⟩ := f.reflect_func F b z haz
    exact ⟨y,⟨b,hb,hy⟩,hfy⟩

theorem Embedding.eval_image {C : Structure L V} {D : Structure L W} (f : Embedding C D)
    {i j : L.Sorts} (t : Term L i j) (x : V) :
    D.eval t (f.point x) = f.point '' C.eval t x := by
  ext z
  constructor
  · exact f.reflect_eval t
  · rintro ⟨y,hy,rfl⟩
    exact f.toHom.map_eval t hy

/-- Totality supplies a genuine, uniquely determined typed value. -/
noncomputable def value (C : Structure L V) (hC : C.Total) {i j : L.Sorts}
    (t : Term L i j) (x : {x : V // C.sort x = i}) : {y : V // C.sort y = j} :=
  let h := C.eval_nonempty hC t x.property
  ⟨h.choose,C.eval_sorted t x.property h.choose_spec⟩

theorem value_mem (C : Structure L V) (hC : C.Total) {i j : L.Sorts}
    (t : Term L i j) (x : {x : V // C.sort x = i}) :
    (C.value hC t x).val ∈ C.eval t x.val :=
  (C.eval_nonempty hC t x.property).choose_spec

theorem value_in_singleton_closure (C : Structure L V) (hC : C.Total)
    {i j : L.Sorts} (t : Term L i j) (x : {x : V // C.sort x = i}) :
    (C.value hC t x).val ∈ C.closureAt x.val :=
  C.eval_closed (C.isClosed_closure {x.val}) t (C.mem_closureAt x.val) (C.value_mem hC t x)

/-- Literal typed values commute with domain-reflecting embeddings. -/
theorem Embedding.value_map {C : Structure L V} {D : Structure L W}
    (f : Embedding C D) (hC : C.Total) (hD : D.Total) {i j : L.Sorts}
    (t : Term L i j) (x : {x : V // C.sort x = i}) :
    f.point (C.value hC t x).val =
      (D.value hD t ⟨f.point x.val,(f.sort_eq x.val).trans x.property⟩).val :=
  D.eval_functional t (f.toHom.map_eval t (C.value_mem hC t x)) (D.value_mem hD t ⟨f.point x.val,(f.sort_eq x.val).trans x.property⟩)

/-- Evaluation in the existing singleton diagram agrees literally with C. -/
theorem singleton_eval_image (C : Structure L V) {i j : L.Sorts} (t : Term L i j) (x : V) :
    Subtype.val '' (C.singletonStructure x).eval t ⟨x,C.mem_closureAt x⟩ = C.eval t x :=
  ((C.inclusion (C.closureAt x) (C.isClosed_closure {x})).eval_image t ⟨x,C.mem_closureAt x⟩).symm

/-- Both terms use the SAME single variable and have the SAME output sort. -/
def Satisfies (C : Structure L V) {i j : L.Sorts} (t s : Term L i j) : Prop :=
  ∀ x : V, C.sort x = i → C.eval t x = C.eval s x

def ValidInClass (K : Class.{u,v} L) {i j : L.Sorts} (t s : Term L i j) : Prop :=
  ∀ {X : Type v} [Finite X] (D : Structure L X), K D → D.Satisfies t s

theorem identity_values (C : Structure L V) (hC : C.Total) {i j : L.Sorts}
    (t s : Term L i j) (h : C.Satisfies t s) (x : {x : V // C.sort x = i}) :
    C.value hC t x = C.value hC s x := by
  apply Subtype.ext
  apply C.eval_functional s
  · exact (h x.val x.property) ▸ C.value_mem hC t x
  · exact C.value_mem hC s x

/-- C23: only the actual completed singleton member is used to transfer
one-variable identities; no ambient completion or binary-arity premise. -/
theorem identities_of_irreducibles [Finite V] (C : Structure L V) {K : Class.{u,v} L}
    (hK : C.IrreduciblesIn K) {i j : L.Sorts} (t s : Term L i j)
    (hValid : ValidInClass K t s) : C.Satisfies t s := by
  intro x hx
  have h := hValid (C.singletonStructure x) (C.singleton_mem_class hK x)
    ⟨x,C.mem_closureAt x⟩ hx
  calc
    C.eval t x = Subtype.val '' (C.singletonStructure x).eval t ⟨x,C.mem_closureAt x⟩ :=
      (C.singleton_eval_image t x).symm
    _ = Subtype.val '' (C.singletonStructure x).eval s ⟨x,C.mem_closureAt x⟩ := congrArg _ h
    _ = C.eval s x := C.singleton_eval_image s x

/-- The transferred identity is an equality of the ACTUAL typed values. -/
theorem identity_values_of_irreducibles [Finite V] (C : Structure L V) {K : Class.{u,v} L}
    (hCompleted : CompletedClass K) (hK : C.IrreduciblesIn K)
    {i j : L.Sorts} (t s : Term L i j) (hValid : ValidInClass K t s)
    (x : {x : V // C.sort x = i}) :
    C.value (C.total_of_irreducibles hCompleted hK) t x =
      C.value (C.total_of_irreducibles hCompleted hK) s x :=
  C.identity_values _ t s (C.identities_of_irreducibles hK t s hValid) x

end CCO.UnarySupport.Structure
