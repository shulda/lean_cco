import CCO.CloneSAP.Basic

/-!
# B060 actual STRONG diversity multiplication by pure clone colours

Here `c` is literally the new diversity atom between two
different clones of the SAME actual owner, never equality.
The STRONG product is the set of triangles with three pairwise
distinct real vertices. Unlike RAW represented multiplication,
`c*c` does not contain the logical diagonal.

The equations hold directly in the full pure-clone source, even
without AP, SAP, CCO, or a generic finite-exact Ramsey theorem.
-/

universe u v w
namespace CCO.CloneTupleGeometry

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- B060 N06/N07: shifting the input of a literal old fine atom
to a distinct clone leaves the old fine atom exactly unchanged,
with no extra equality case or extra diversity atom. -/
theorem pure_clone_strong_left {i j : ι} (a : S.Atom i j) :
    (CloneSAP.source S).product
      ({Sum.inr ⟨rfl⟩} : (CloneSAP.source S).Menu i i)
      ({Sum.inl a} : (CloneSAP.source S).Menu i j) =
      ({Sum.inl a} : (CloneSAP.source S).Menu i j) := by
  ext b
  constructor
  · rintro ⟨p, hp, q, hq, x, y, z, hxy, hyz, hxz⟩
    have hp' : p = Sum.inr ⟨rfl⟩ := Set.mem_singleton_iff.mp hp
    have hq' : q = Sum.inl a := Set.mem_singleton_iff.mp hq
    subst p
    subst q
    have howner : x.1 = y.1 :=
      ((CloneSAP.source_clone_iff S x y).mp hxy).1
    have hOld : S.colour y.1 z.1 = some a :=
      (CloneSAP.colour_old_iff S y z a).mp hyz
    have hOld' : S.colour x.1 z.1 = some a := by
      simpa only [howner] using hOld
    have hOut : (CloneSAP.source S).colour x z = some (Sum.inl a) :=
      (CloneSAP.colour_old_iff S x z a).mpr hOld'
    exact Set.mem_singleton_iff.mpr (Option.some.inj (hxz.symm.trans hOut))
  · intro hb
    have heq : b = Sum.inl a := Set.mem_singleton_iff.mp hb
    subst b
    obtain ⟨x, y, hcol⟩ := S.realized a
    let p : CloneSAP.Carrier X i := (x, 0)
    let q : CloneSAP.Carrier X i := (x, 1)
    let r : CloneSAP.Carrier X j := (y, 0)
    refine ⟨Sum.inr ⟨rfl⟩, by simp, Sum.inl a, by simp, p, q, r, ?_, ?_, ?_⟩
    · exact (CloneSAP.source_clone_iff S p q).mpr ⟨rfl, by decide⟩
    · exact (CloneSAP.colour_old_iff S q r a).mpr hcol
    · exact (CloneSAP.colour_old_iff S p r a).mpr hcol

/-- B060 N06/N07: shifting the output endpoint to a fresh clone
also preserves exactly the genuine original fine diversity atom. -/
theorem pure_clone_strong_right {i j : ι} (a : S.Atom i j) :
    (CloneSAP.source S).product
      ({Sum.inl a} : (CloneSAP.source S).Menu i j)
      ({Sum.inr ⟨rfl⟩} : (CloneSAP.source S).Menu j j) =
      ({Sum.inl a} : (CloneSAP.source S).Menu i j) := by
  ext b
  constructor
  · rintro ⟨p, hp, q, hq, x, y, z, hxy, hyz, hxz⟩
    have hp' : p = Sum.inl a := Set.mem_singleton_iff.mp hp
    have hq' : q = Sum.inr ⟨rfl⟩ := Set.mem_singleton_iff.mp hq
    subst p
    subst q
    have howner : y.1 = z.1 :=
      ((CloneSAP.source_clone_iff S y z).mp hyz).1
    have hOld : S.colour x.1 y.1 = some a :=
      (CloneSAP.colour_old_iff S x y a).mp hxy
    have hOld' : S.colour x.1 z.1 = some a := by
      simpa only [← howner] using hOld
    have hOut : (CloneSAP.source S).colour x z = some (Sum.inl a) :=
      (CloneSAP.colour_old_iff S x z a).mpr hOld'
    exact Set.mem_singleton_iff.mpr (Option.some.inj (hxz.symm.trans hOut))
  · intro hb
    have heq : b = Sum.inl a := Set.mem_singleton_iff.mp hb
    subst b
    obtain ⟨x, y, hcol⟩ := S.realized a
    let p : CloneSAP.Carrier X i := (x, 0)
    let q : CloneSAP.Carrier X j := (y, 0)
    let r : CloneSAP.Carrier X j := (y, 1)
    refine ⟨Sum.inl a, by simp, Sum.inr ⟨rfl⟩, by simp, p, q, r, ?_, ?_, ?_⟩
    · exact (CloneSAP.colour_old_iff S p q a).mpr hcol
    · exact (CloneSAP.source_clone_iff S q r).mpr ⟨rfl, by decide⟩
    · exact (CloneSAP.colour_old_iff S p r a).mpr hcol

/-- The genuine STRONG diversity-only square is the singleton clone
atom. This is distinct from the FULL represented identity-inclusive
formula `c;c=K` already proved in B045. -/
theorem pure_clone_strong_square (i : ι) :
    (CloneSAP.source S).product
      ({Sum.inr ⟨rfl⟩} : (CloneSAP.source S).Menu i i)
      ({Sum.inr ⟨rfl⟩} : (CloneSAP.source S).Menu i i) =
      ({Sum.inr ⟨rfl⟩} : (CloneSAP.source S).Menu i i) := by
  ext a
  constructor
  · rintro ⟨p, hp, q, hq, x, y, z, hxy, hyz, hxz⟩
    have hp' : p = Sum.inr ⟨rfl⟩ := Set.mem_singleton_iff.mp hp
    have hq' : q = Sum.inr ⟨rfl⟩ := Set.mem_singleton_iff.mp hq
    subst p
    subst q
    have hownerxy : x.1 = y.1 :=
      ((CloneSAP.source_clone_iff S x y).mp hxy).1
    have howneryz : y.1 = z.1 :=
      ((CloneSAP.source_clone_iff S y z).mp hyz).1
    have hownerxz : x.1 = z.1 := hownerxy.trans howneryz
    have hindex : x.2 ≠ z.2 := by
      intro hi
      have hpair : x = z := Prod.ext hownerxz hi
      subst z
      have hnone : (CloneSAP.source S).colour x x = none :=
        ((CloneSAP.source S).colour_none_iff x x).mpr rfl
      rw [hnone] at hxz
      cases hxz
    have hClone : (CloneSAP.source S).colour x z =
        some (Sum.inr ⟨rfl⟩) :=
      (CloneSAP.source_clone_iff S x z).mpr ⟨hownerxz, hindex⟩
    exact Set.mem_singleton_iff.mpr (Option.some.inj (hxz.symm.trans hClone))
  · intro ha
    have heq : a = Sum.inr ⟨rfl⟩ := Set.mem_singleton_iff.mp ha
    subst a
    obtain ⟨p⟩ := S.nonemptySort i
    let x : CloneSAP.Carrier X i := (p, 0)
    let y : CloneSAP.Carrier X i := (p, 1)
    let z : CloneSAP.Carrier X i := (p, 2)
    refine ⟨Sum.inr ⟨rfl⟩, by simp, Sum.inr ⟨rfl⟩, by simp,
      x, y, z, ?_, ?_, ?_⟩
    · exact (CloneSAP.source_clone_iff S x y).mpr ⟨rfl, by decide⟩
    · exact (CloneSAP.source_clone_iff S y z).mpr ⟨rfl, by decide⟩
    · exact (CloneSAP.source_clone_iff S x z).mpr ⟨rfl, by decide⟩

/-- The literal two-sided clone cylinder around every old fine atom is
exactly its old fine atom, with no hidden quotient or abstract exactness
hypothesis. Repeated source and target sorts are included. -/
theorem pure_clone_strong_sandwich {i j : ι} (a : S.Atom i j) :
    (CloneSAP.source S).product
      ((CloneSAP.source S).product
        ({Sum.inr ⟨rfl⟩} : (CloneSAP.source S).Menu i i)
        ({Sum.inl a} : (CloneSAP.source S).Menu i j))
      ({Sum.inr ⟨rfl⟩} : (CloneSAP.source S).Menu j j) =
      ({Sum.inl a} : (CloneSAP.source S).Menu i j) := by
  rw [pure_clone_strong_left S a, pure_clone_strong_right S a]

end CCO.CloneTupleGeometry
