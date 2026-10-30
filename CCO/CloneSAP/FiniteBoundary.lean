import CCO.CloneSAP.Homogeneity

/-! C35. Finite clone windows are not unbounded SAP sources.
The obstruction uses actual finite induced spans and the literal capacity
of a fibre, without homogeneity or old SAP assumptions. -/

universe u v w
namespace CCO.CloneSAP.FiniteBoundary
variable {ι : Type u} {X : ι → Type v}
abbrev Carrier (X : ι → Type v) (m : ℕ) (i : ι) := X i × Fin m

def up (m : ℕ) (p : Sigma (Carrier X m)) : Sigma (CloneSAP.Carrier X) :=
  ⟨p.1, (p.2.1, p.2.2.val)⟩

theorem up_injective (m : ℕ) : Function.Injective (up (X := X) m) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h
  have hi : i = j := congrArg Sigma.fst h
  subst j
  have hp : (x.1,x.2.val) = (y.1,y.2.val) := eq_of_heq (Sigma.mk.inj h).2
  have ho := congrArg Prod.fst hp
  have hn : x.2 = y.2 := Fin.ext (congrArg Prod.snd hp)
  exact congrArg (Sigma.mk i) (Prod.ext ho hn)

noncomputable def source (S : AtomicSource ι X) (m : ℕ) (hm : 2 ≤ m) :
    AtomicSource ι (Carrier X m) where
  Atom := CloneSAP.Atom S
  finiteSort := S.finiteSort
  finiteAtom := (CloneSAP.source S).finiteAtom
  nonemptySort i := by
    obtain ⟨x⟩ := S.nonemptySort i
    exact ⟨x,⟨0,by omega⟩⟩
  conv := (CloneSAP.source S).conv
  conv_invol := (CloneSAP.source S).conv_invol
  symmetricLoop := (CloneSAP.source S).symmetricLoop
  colour x y := CloneSAP.colour S (x.1,x.2.val) (y.1,y.2.val)
  colour_none_iff x y := by
    rw [CloneSAP.colour_none_iff]
    change up m ⟨_,x⟩ = up m ⟨_,y⟩ ↔ _
    exact (up_injective m).eq_iff
  colour_swap x y a := (CloneSAP.source S).colour_swap (x.1,x.2.val) (y.1,y.2.val) a
  realized := by
    intro i j a
    cases a with
    | inl a =>
      obtain ⟨x,y,h⟩ := S.realized a
      refine ⟨(x,⟨0,by omega⟩),(y,⟨0,by omega⟩),?_⟩
      exact (colour_old_iff S _ _ a).mpr h
    | inr e =>
      rcases e with ⟨e⟩
      subst j
      obtain ⟨x⟩ := S.nonemptySort i
      refine ⟨(x,⟨0,by omega⟩),(x,⟨1,by omega⟩),?_⟩
      exact (colour_clone_iff S _ _ ⟨rfl⟩).mpr ⟨rfl,by change (0 : ℕ) ≠ 1; exact Nat.zero_ne_one⟩

variable (S : AtomicSource.{u,v,w} ι X) (m : ℕ) (hm : 2 ≤ m) (i : ι) (q : X i)

def fibrePoint (n : Fin m) : Sigma (Carrier X m) := ⟨i,(q,n)⟩

def fibre : FiniteInduced (X := Carrier X m) where
  vertices := Set.range (fibrePoint m i q)
  finite_vertices := Set.finite_range _

def fibreVertex (n : Fin m) : (fibre m i q).vertices := ⟨fibrePoint m i q n,⟨n,rfl⟩⟩

def base : FiniteInduced (X := Carrier X m) where
  vertices := {fibrePoint m i q ⟨0,by omega⟩}
  finite_vertices := Set.finite_singleton _

def baseToFibre : InducedEmbedding (source S m hm) (base m hm i q) (fibre m i q) where
  toEmbedding :=
    { toFun p := ⟨p.val, by rw [p.property]; exact ⟨_,rfl⟩⟩
      inj' := fun a b h => Subtype.ext
        (congrArg (fun p : (fibre m i q).vertices => p.val) h) }
  preserves_sort _ := rfl
  preserves_colours _ _ := rfl

private theorem owner_preserved {A B : FiniteInduced (X := Carrier X m)}
    (e : InducedEmbedding (source S m hm) A B) (p r : A.vertices)
    (h : CloneSAP.owner (up m p.val) = CloneSAP.owner (up m r.val)) :
    CloneSAP.owner (up m (e.toEmbedding p).val) =
      CloneSAP.owner (up m (e.toEmbedding r).val) := by
  have hc := e.preserves_colours p r
  change taggedColour (CloneSAP.source S) (up m p.val) (up m r.val) =
    taggedColour (CloneSAP.source S) (up m (e.toEmbedding p).val)
      (up m (e.toEmbedding r).val) at hc
  have ho := tagged_owner_eq S hc
  have flags := congrArg (fun z : Σ a, Σ b, Option (S.Atom a b) => z.2.2.isNone) ho
  have old : (S.colour (CloneSAP.owner (up m p.val)).2
      (CloneSAP.owner (up m r.val)).2).isNone = true := by
    rw [Option.isNone_iff_eq_none, S.colour_none_iff]
    exact h
  have new := flags ▸ old
  exact (S.colour_none_iff _ _).mp (Option.isNone_iff_eq_none.mp new)

private theorem point_eq_of_owner_index (p r : Sigma (Carrier X m))
    (h : CloneSAP.owner (up m p) = CloneSAP.owner (up m r))
    (hn : p.2.2 = r.2.2) : p = r := by
  apply up_injective m
  apply pointEquiv.injective
  exact Prod.ext h (congrArg Fin.val hn)

/-- For every fixed m≥2, two full c-fibres over a singleton have no real
strong amalgam. The old source may be finite and need not be homogeneous. -/
theorem not_ageSAP (i : ι) (q : X i) : ¬ AgeSAP (source S m hm) := by
  intro sap
  let A := base m hm i q
  let B := fibre m i q
  let e := baseToFibre S m hm i q
  obtain ⟨D,f,g,agree,strong⟩ := sap.strong_amalgamate A B B e e
  let imageF (n : Fin m) := f.toEmbedding (fibreVertex m i q n)
  let imageG (n : Fin m) := g.toEmbedding (fibreVertex m i q n)
  let idx (n : Fin m) := (imageF n).val.2.2
  have inj : Function.Injective idx := by
    intro a b hab
    have ho := owner_preserved S m hm f (fibreVertex m i q a) (fibreVertex m i q b) rfl
    have hp := point_eq_of_owner_index m (imageF a).val (imageF b).val ho hab
    have hh := f.toEmbedding.injective (Subtype.ext hp)
    exact congrArg (fun p : B.vertices => p.val.2.2) hh
  have surj : Function.Surjective idx := (Finite.injective_iff_surjective).mp inj
  let one : Fin m := ⟨1,by omega⟩
  let zero : Fin m := ⟨0,by omega⟩
  obtain ⟨n,hn⟩ := surj (imageG one).val.2.2
  let a : A.vertices := ⟨fibrePoint m i q zero,rfl⟩
  have hzero : imageF zero = imageG zero := agree a
  have hoF := owner_preserved S m hm f (fibreVertex m i q n) (fibreVertex m i q zero) rfl
  have hoG := owner_preserved S m hm g (fibreVertex m i q zero) (fibreVertex m i q one) rfl
  have ho : CloneSAP.owner (up m (imageF n).val) =
      CloneSAP.owner (up m (imageG one).val) := by
    exact hoF.trans ((congrArg (fun p : D.vertices => CloneSAP.owner (up m p.val)) hzero).trans hoG)
  have he : imageF n = imageG one := Subtype.ext (point_eq_of_owner_index m _ _ ho hn)
  obtain ⟨c,_,hc⟩ := strong (fibreVertex m i q n) (fibreVertex m i q one) he
  have hz : c.val = fibrePoint m i q zero := c.property
  have hidx := congrArg (fun p : B.vertices => p.val.2.2.val) hc
  change c.val.2.2.val = 1 at hidx
  rw [hz] at hidx
  exact Nat.zero_ne_one hidx

/-- With exactly two indices the full diversity square is equality,
not the owner kernel. -/
def twoCloneRel {A : Type*} (x y : A × Fin 2) : Prop := x.1 = y.1 ∧ x.2 ≠ y.2

theorem two_clone_square {A : Type*} :
    TRel.comp (X := fun _ : Unit => A × Fin 2)
      (i := ()) (j := ()) (k := ()) twoCloneRel twoCloneRel = Eq := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩
    apply Prod.ext (hxz.1.trans hzy.1)
    have hx := x.2.isLt
    have hy := y.2.isLt
    have hz := z.2.isLt
    have hxn : x.2.val ≠ z.2.val := fun he => hxz.2 (Fin.ext he)
    have hzn : z.2.val ≠ y.2.val := fun he => hzy.2 (Fin.ext he)
    apply Fin.ext
    omega
  · intro he
    subst y
    let other : Fin 2 := if x.2 = 0 then 1 else 0
    have hn : x.2 ≠ other := by
      dsimp [other]
      split_ifs with h
      · rw [h]; decide
      · exact h
    exact ⟨(x.1,other),⟨rfl,hn⟩,⟨rfl,hn.symm⟩⟩

theorem two_clones_fail_kernel {A : Type*} (a : A) :
    ¬ TRel.comp (X := fun _ : Unit => A × Fin 2) (i := ()) (j := ()) (k := ())
      twoCloneRel twoCloneRel (a,0) (a,1) := by
  rw [two_clone_square]
  intro he
  have hi := congrArg (fun p : A × Fin 2 => p.2.val) he
  exact Nat.zero_ne_one hi

def boundedCloneRel {A : Type*} {m : ℕ} (x y : A × Fin m) : Prop :=
  x.1 = y.1 ∧ x.2 ≠ y.2

/-- Three actual available indices suffice for the bounded c;c calculation.
This supplies no unbounded freshness or SAP theorem for finite windows. -/
theorem bounded_clone_square {A : Type*} {m : ℕ} (hm : 3 ≤ m) :
    TRel.comp (X := fun _ : Unit => A × Fin m) (i := ()) (j := ()) (k := ())
      boundedCloneRel boundedCloneRel = (fun x y => x.1 = y.1) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩
    exact hxz.1.trans hzy.1
  · intro ho
    have fresh : ∃ n : Fin m, x.2 ≠ n ∧ n ≠ y.2 := by
      by_cases h0 : x.2.val ≠ 0 ∧ y.2.val ≠ 0
      · exact ⟨⟨0,by omega⟩,fun h => h0.1 (congrArg Fin.val h),
          fun h => h0.2 (congrArg Fin.val h).symm⟩
      by_cases h1 : x.2.val ≠ 1 ∧ y.2.val ≠ 1
      · exact ⟨⟨1,by omega⟩,fun h => h1.1 (congrArg Fin.val h),
          fun h => h1.2 (congrArg Fin.val h).symm⟩
      have h2 : x.2.val ≠ 2 ∧ y.2.val ≠ 2 := by omega
      exact ⟨⟨2,by omega⟩,fun h => h2.1 (congrArg Fin.val h),
        fun h => h2.2 (congrArg Fin.val h).symm⟩
    obtain ⟨n,hx,hy⟩ := fresh
    exact ⟨(x.1,n),⟨rfl,hx⟩,⟨ho,hy⟩⟩

/-- One clone is literally the old carrier; no universal SAP failure is asserted. -/
def oneCloneEquiv (A : Type*) : (A × Fin 1) ≃ A where
  toFun := Prod.fst
  invFun a := (a,0)
  left_inv x := by exact Prod.ext rfl (Fin.eq_zero _).symm
  right_inv _ := rfl

theorem one_clone_empty {A : Type*} (x y : A × Fin 1) : ¬ boundedCloneRel x y := by
  intro h
  exact h.2 (Fin.eq_zero _ |>.trans (Fin.eq_zero _).symm)

theorem one_clone_old_colour {i j : ι} (x : X i × Fin 1) (y : X j × Fin 1) :
    CloneSAP.colour S (x.1,x.2.val) (y.1,y.2.val) =
      (S.colour x.1 y.1).map Sum.inl := by
  classical
  unfold CloneSAP.colour
  have hx : x.2.val = 0 := congrArg Fin.val (Fin.eq_zero x.2)
  have hy : y.2.val = 0 := congrArg Fin.val (Fin.eq_zero y.2)
  by_cases h : S.colour x.1 y.1 = none <;> simp [hx,hy,h]

end CCO.CloneSAP.FiniteBoundary
