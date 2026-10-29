import CCO.HKNReservoir.PacketControl

universe u v w z x y
namespace CCO.HKNReservoir
open AllThoseEPPA
variable {B : Type u} {K : Type v} [Group K] {Atom : Type w}
variable {V : Type x} {W : Type y} {Γ : Type z} [Group Γ]

/-- Laws of the ACTUAL source only; none is imposed on unrestricted output. -/
structure RegularData (D : Data B K Atom V) : Prop where
  one : ∀ x, D.move 1 x = x
  mul : ∀ g h x, D.move (g*h) x = D.move g (D.move h x)
  free : ∀ x, Function.Injective (fun g => D.move g x)

namespace PacketRecovery
variable (tag : Γ →* Equiv.Perm B) (D : Data B K Atom V)
variable (E : Structure (Signature B K Atom) W)
variable (hLocal : LocallyInSource tag (encode D) E)

/-- The WHOLE one-generated CLOSED piece embeds into the actual source. -/
noncomputable def closureEmbedding (x : W) :
    Structure.Embedding (action tag) (E.closureAt x) (encode D) :=
  Classical.choice (hLocal (E.closureAtSet x) (E.isClosed_closureSet {x}) (E.closureAt_isIrreducible x))

/-- Exact embedding equality for the full set-valued unary output. -/
theorem embedding_func_image {P : Set W} (hP : E.IsClosed P)
    (e : Structure.Embedding (action tag) (E.induce P hP) (encode D)) (k : K) (x : P) :
    e.toFun '' {y : P | y.val ∈ E.func (.translate k) (fun _ => x.val)} = {D.move k (e x)} := by
  simpa only [Structure.induce,Structure.imageSet,action_translate,encode_translate,Function.comp_def]
    using e.map_func (.translate k) (fun _ => x)

include hLocal in
theorem existsUnique_value (k : K) (x : W) :
    ∃! y, y ∈ E.func (.translate k) (fun _ => x) := by
  let P := E.closureAtSet x
  have hP : E.IsClosed P := E.isClosed_closureSet {x}
  let e := closureEmbedding tag D E hLocal x
  let x₀ : P := ⟨x,E.mem_closureAtSet x⟩
  have he := embedding_func_image tag D E hP e k x₀
  have hm : D.move k (e x₀) ∈ e.toFun '' {y : P | y.val ∈ E.func (.translate k) (fun _ => x)} := by
    rw [he]; exact Set.mem_singleton _
  obtain ⟨y,hy,_⟩ := hm
  refine ⟨y.val,hy,?_⟩
  intro z hz
  have hzP : z ∈ P := hP (.translate k) (fun _ => x) (fun _ => E.mem_closureAtSet x) hz
  have hez : e ⟨z,hzP⟩ ∈ ({D.move k (e x₀)} : Set V) :=
    he ▸ (show e ⟨z,hzP⟩ ∈ e.toFun '' {y : P | y.val ∈ E.func (.translate k) (fun _ => x)} from
      ⟨⟨z,hzP⟩,hz,rfl⟩)
  have hey : e y ∈ ({D.move k (e x₀)} : Set V) :=
    he ▸ (show e y ∈ e.toFun '' {y : P | y.val ∈ E.func (.translate k) (fun _ => x)} from ⟨y,hy,rfl⟩)
  exact congrArg Subtype.val (e.injective ((Set.mem_singleton_iff.mp hez).trans
    (Set.mem_singleton_iff.mp hey).symm))

noncomputable def move (k : K) (x : W) : W := (existsUnique_value tag D E hLocal k x).choose

theorem move_mem (k : K) (x : W) : move tag D E hLocal k x ∈ E.func (.translate k) (fun _ => x) :=
  (existsUnique_value tag D E hLocal k x).choose_spec.1

theorem func_value (k : K) (x : W) :
    E.func (.translate k) (fun _ => x) = {move tag D E hLocal k x} := by
  ext y
  constructor
  · intro hy
    exact (existsUnique_value tag D E hLocal k x).choose_spec.2 y hy
  · rintro rfl
    exact move_mem tag D E hLocal k x

theorem move_closed {P : Set W} (hP : E.IsClosed P) (k : K) {x : W} (hx : x ∈ P) :
    move tag D E hLocal k x ∈ P :=
  hP (.translate k) (fun _ => x) (fun _ => hx) (move_mem tag D E hLocal k x)

theorem embedding_move {P : Set W} (hP : E.IsClosed P)
    (e : Structure.Embedding (action tag) (E.induce P hP) (encode D)) (k : K) (x : P) :
    e ⟨move tag D E hLocal k x.val,move_closed tag D E hLocal hP k x.property⟩ = D.move k (e x) := by
  have h : e ⟨move tag D E hLocal k x.val,move_closed tag D E hLocal hP k x.property⟩ ∈
      e.toFun '' {y : P | y.val ∈ E.func (.translate k) (fun _ => x.val)} :=
    ⟨_,move_mem tag D E hLocal k x.val,rfl⟩
  rw [embedding_func_image tag D E hP e k x] at h
  exact h

variable (hD : RegularData D)

include hD in
theorem move_one (x : W) : move tag D E hLocal 1 x = x := by
  let hP : E.IsClosed (E.closureAtSet x) := E.isClosed_closureSet {x}
  let e := closureEmbedding tag D E hLocal x
  let x₀ : E.closureAtSet x := ⟨x,E.mem_closureAtSet x⟩
  have h := embedding_move tag D E hLocal hP e 1 x₀
  rw [hD.one] at h
  exact congrArg Subtype.val (e.injective h)

include hD in
theorem move_mul (g h : K) (x : W) :
    move tag D E hLocal (g*h) x = move tag D E hLocal g (move tag D E hLocal h x) := by
  let hP : E.IsClosed (E.closureAtSet x) := E.isClosed_closureSet {x}
  let e := closureEmbedding tag D E hLocal x
  let x₀ : E.closureAtSet x := ⟨x,E.mem_closureAtSet x⟩
  let xh : E.closureAtSet x := ⟨move tag D E hLocal h x,move_closed tag D E hLocal hP h x₀.property⟩
  have he : e ⟨move tag D E hLocal (g*h) x,move_closed tag D E hLocal hP (g*h) x₀.property⟩ =
      e ⟨move tag D E hLocal g xh.val,move_closed tag D E hLocal hP g xh.property⟩ := by
    calc
      _ = D.move (g*h) (e x₀) := embedding_move tag D E hLocal hP e (g*h) x₀
      _ = D.move g (D.move h (e x₀)) := hD.mul g h _
      _ = D.move g (e xh) := congrArg (D.move g) (embedding_move tag D E hLocal hP e h x₀).symm
      _ = _ := (embedding_move tag D E hLocal hP e g xh).symm
  exact congrArg Subtype.val (e.injective he)

include hD in
theorem move_free (x : W) : Function.Injective (fun g => move tag D E hLocal g x) := by
  intro g h he
  let hP : E.IsClosed (E.closureAtSet x) := E.isClosed_closureSet {x}
  let e := closureEmbedding tag D E hLocal x
  let x₀ : E.closureAtSet x := ⟨x,E.mem_closureAtSet x⟩
  apply hD.free (e x₀)
  calc
    _ = e ⟨move tag D E hLocal g x,move_closed tag D E hLocal hP g x₀.property⟩ :=
      (embedding_move tag D E hLocal hP e g x₀).symm
    _ = e ⟨move tag D E hLocal h x,move_closed tag D E hLocal hP h x₀.property⟩ :=
      congrArg e.toFun (Subtype.ext he)
    _ = _ := embedding_move tag D E hLocal hP e h x₀

@[instance_reducible] noncomputable def action : MulAction K W where
  smul := move tag D E hLocal
  one_smul := move_one tag D E hLocal hD
  mul_smul := move_mul tag D E hLocal hD

def orbit (x : W) : Set W := Set.range (fun k => move tag D E hLocal k x)

include hD in
theorem orbit_closed (x : W) : E.IsClosed (orbit tag D E hLocal x) := by
  intro n F xs hxs y hy
  cases F with
  | translate k =>
    have ht : xs = (fun _ => xs 0) := funext (fun i => congrArg xs (Subsingleton.elim _ _))
    have hv : E.func (.translate k) xs = {move tag D E hLocal k (xs 0)} :=
      (congrArg (fun t : Fin 1 → W => E.func (.translate k) t) ht).trans
        (func_value tag D E hLocal k (xs 0))
    have hym : y = move tag D E hLocal k (xs 0) := Set.mem_singleton_iff.mp
      (Eq.mp (congrArg (fun T : Set W => y ∈ T) hv) hy)
    obtain ⟨h,hh⟩ := hxs 0
    refine ⟨k*h,?_⟩
    exact (move_mul tag D E hLocal hD k h x).trans
      ((congrArg (move tag D E hLocal k) hh).trans hym.symm)

include hD in
theorem closure_eq_orbit (x : W) : E.closureAtSet x = orbit tag D E hLocal x := by
  apply Set.Subset.antisymm
  · apply E.closureSet_minimal (orbit_closed tag D E hLocal hD x)
    intro y hy
    have he : y = x := hy
    subst y
    exact ⟨1,move_one tag D E hLocal hD x⟩
  · rintro y ⟨k,rfl⟩
    exact move_closed tag D E hLocal (E.isClosed_closureSet {x}) k (E.mem_closureAtSet x)

noncomputable def owner (x : W) : B :=
  (tag (closureEmbedding tag D E hLocal x).lang).symm
    (D.owner (closureEmbedding tag D E hLocal x ⟨x,E.mem_closureAtSet x⟩))

theorem owner_iff (x : W) (b : B) : E.rel (.owner b) (fun _ => x) ↔ owner tag D E hLocal x = b := by
  let e := closureEmbedding tag D E hLocal x
  let x₀ : E.closureAtSet x := ⟨x,E.mem_closureAtSet x⟩
  have he := e.map_rel_iff (.owner b) (fun _ => x₀)
  change D.owner (e x₀) = tag e.lang b ↔ E.rel (.owner b) (fun _ => x) at he
  rw [← he]
  exact ((tag e.lang).symm_apply_eq).symm

/-- Every output point has exactly ONE actual owner relation. -/
theorem unique_owner (hLocal : LocallyInSource tag (encode D) E) (x : W) : ∃! b : B, E.rel (.owner b) (fun _ => x) := by
  refine ⟨owner tag D E hLocal x,(owner_iff tag D E hLocal x _).mpr rfl,?_⟩
  intro b hb
  exact ((owner_iff tag D E hLocal x b).mp hb).symm


/-- The recovered interpretation preserves precisely the original partial
records. It adds no missing relation tuples or completed colours. -/
noncomputable def data : Data B K Atom W where
  owner := owner tag D E hLocal
  fine a x y := E.rel (.fine a) (![x,y])
  move := move tag D E hLocal

theorem encode_data : encode (data tag D E hLocal) = E := by
  apply (show ∀ (C F : Structure (Signature B K Atom) W), @C.rel = @F.rel → @C.func = @F.func → C=F from by
    intro C F hr hf
    rcases C with ⟨cr,cf⟩
    rcases F with ⟨er,ef⟩
    dsimp only at hr hf
    exact congrArg₂ (@Structure.mk (Signature B K Atom) W) hr hf)
  · funext n R xs
    cases R with
    | owner b =>
      change (owner tag D E hLocal (xs 0) = b) = E.rel (.owner b) xs
      have ht : xs = (fun _ => xs 0) := funext (fun i => congrArg xs (Subsingleton.elim _ _))
      have he := congrArg (E.rel (.owner b)) ht
      exact propext ((owner_iff tag D E hLocal (xs 0) b).symm.trans (Iff.of_eq he.symm))
    | fine a =>
      change E.rel (.fine a) (![xs 0,xs 1]) = E.rel (.fine a) xs
      apply congrArg (E.rel (.fine a))
      funext i
      fin_cases i <;> rfl
  · funext n F xs
    cases F with
    | translate k =>
      change ({move tag D E hLocal k (xs 0)} : Set W) = E.func (.translate k) xs
      have ht : xs = (fun _ => xs 0) := funext (fun i => congrArg xs (Subsingleton.elim _ _))
      exact ((congrArg (E.func (.translate k)) ht).trans (func_value tag D E hLocal k (xs 0))).symm

include hD in
theorem regular_data : RegularData (data tag D E hLocal) where
  one := move_one tag D E hLocal hD
  mul := move_mul tag D E hLocal hD
  free := move_free tag D E hLocal hD

include hD in
theorem orbit_move (g : K) (x : W) :
    orbit tag D E hLocal (move tag D E hLocal g x) = orbit tag D E hLocal x := by
  apply Set.Subset.antisymm
  · rintro y ⟨h,rfl⟩
    exact ⟨h*g,move_mul tag D E hLocal hD h g x⟩
  · rintro y ⟨h,rfl⟩
    refine ⟨h*g⁻¹,?_⟩
    change move tag D E hLocal (h*g⁻¹) (move tag D E hLocal g x) = move tag D E hLocal h x
    rw [← move_mul tag D E hLocal hD]
    simp only [mul_assoc,inv_mul_cancel,mul_one]

include hD in
theorem orbit_eq_of_mem {x y : W} (hy : y ∈ orbit tag D E hLocal x) :
    orbit tag D E hLocal y = orbit tag D E hLocal x := by
  obtain ⟨g,rfl⟩ := hy
  exact orbit_move tag D E hLocal hD g x

include hLocal hD in
theorem packet_partition (x y : W) :
    E.closureAtSet x = E.closureAtSet y ∨ Disjoint (E.closureAtSet x) (E.closureAtSet y) := by
  rw [closure_eq_orbit tag D E hLocal hD,closure_eq_orbit tag D E hLocal hD]
  by_cases hd : Disjoint (orbit tag D E hLocal x) (orbit tag D E hLocal y)
  · exact Or.inr hd
  · obtain ⟨z,hzx,hzy⟩ := Set.not_disjoint_iff.mp hd
    exact Or.inl ((orbit_eq_of_mem tag D E hLocal hD hzx).symm.trans
      (orbit_eq_of_mem tag D E hLocal hD hzy))

include hLocal hD in
theorem closure_card (x : W) : Nat.card (E.closureAtSet x) = Nat.card K := by
  let f : K → E.closureAtSet x := fun k =>
    ⟨move tag D E hLocal k x,move_closed tag D E hLocal (E.isClosed_closureSet {x}) k (E.mem_closureAtSet x)⟩
  have hi : Function.Injective f := fun k h he =>
    move_free tag D E hLocal hD x (congrArg Subtype.val he)
  have hs : Function.Surjective f := by
    intro y
    have hy : y.val ∈ orbit tag D E hLocal x := (closure_eq_orbit tag D E hLocal hD x) ▸ y.property
    obtain ⟨k,hk⟩ := hy
    exact ⟨k,Subtype.ext hk⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm

end PacketRecovery
end CCO.HKNReservoir
