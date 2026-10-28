import CCO.RealHull.Geometry.Supports
import CCO.RealHull.Geometry.IndexedOnePoint

/-! Relative separator on the literal original support palette. All triangles
are placed about ONE real edge, then the second apex is realised over the
ENTIRE same finite complete anchor. Ordinary homogeneity+CCO suffice. -/
universe v w t
namespace CCO.RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M]

theorem relative_separator (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
    (R : Support S) (P : Finset (Atom S))
    (hcover : ∀ c : Atom S, (∀ p ∈ P, c ∈ square S p) → c ∈ R.val)
    (u v : Atom S) (hnot : ¬ SupportOrbit S R u v) :
    ∃ p ∈ P, Disjoint (row S p u) (row S p v) := by
  classical
  by_contra hsep
  have hcommon : ∀ p : ↥P, (row S p.val u ∩ row S p.val v).Nonempty := by
    intro p
    by_contra hn
    apply hsep
    refine ⟨p.val,p.property,Set.disjoint_left.mpr ?_⟩
    exact fun c hu hv => hn ⟨c,hu,hv⟩
  choose d hd using hcommon
  have hne : u ≠ v := by
    rintro rfl
    exact hnot (supportOrbit_refl S R u)
  obtain ⟨x,z,hxz⟩ := S.realized u
  have hpoints : ∀ p : ↥P, ∃ a : M,
      col S x a = some p.val ∧ col S a z = some (d p) := by
    intro p
    exact triangle_over_pair S H (triangle_swap_first S ((mem_row S _ _ _).mp (hd p).1)) hxz
  choose a hxa haz using hpoints
  have hanz (p : ↥P) : a p ≠ z := by
    intro he
    have hh := haz p
    rw [he,(col_none S z z).mpr rfl] at hh
    cases hh
  have hainj : Function.Injective a := by
    intro p q he
    apply Subtype.ext
    exact Option.some.inj ((hxa p).symm.trans ((congrArg (col S x) he).trans (hxa q)))
  let e : Option ↥P ↪ M := {
    toFun := fun b => match b with | none => z | some p => a p
    inj' := by
      intro b c he
      cases b with
      | none =>
        cases c with
        | none => rfl
        | some q => exact False.elim (hanz q he.symm)
      | some p =>
        cases c with
        | none => exact False.elim (hanz p he)
        | some q => exact congrArg some (hainj he)
  }
  let q : Option ↥P → Atom S := fun b => match b with | none => v | some p => p.val
  have htri : ∀ b c : Option ↥P, b ≠ c → ∀ r : Atom S,
      col S (e b) (e c) = some r → S.Triangle (q b) r (q c) := by
    intro b c hbc r hr
    cases b with
    | none =>
      cases c with
      | none => exact False.elim (hbc rfl)
      | some p =>
        have he : r = d p := Option.some.inj (hr.symm.trans ((col_symm S z (a p)).trans (haz p)))
        subst r
        exact triangle_cycle S ((mem_row S _ _ _).mp (hd p).2)
    | some p =>
      cases c with
      | none =>
        have he : r = d p := Option.some.inj (hr.symm.trans (haz p))
        subst r
        exact triangle_swap_first S ((mem_row S _ _ _).mp (hd p).2)
      | some p' => exact ⟨x,a p,a p',hxa p,hr,hxa p'⟩
  obtain ⟨y,_,hy⟩ := onePointExtension_indexed S H cco e q htri
  have hyz : col S y z = some v := hy none
  have hya (p : ↥P) : col S y (a p) = some p.val := hy (some p)
  have hxy : x ≠ y := by
    intro he
    exact hne (Option.some.inj (hxz.symm.trans ((congrArg (fun t => col S t z) he).trans hyz)))
  obtain ⟨c,hc⟩ := col_some_of_ne S hxy
  have hcR : c ∈ R.val := by
    apply hcover c
    intro p hp
    exact (mem_row S p p c).mpr ⟨x,a ⟨p,hp⟩,y,hxa _,
      (col_symm S (a ⟨p,hp⟩) y).trans (hya _),hc⟩
  apply hnot
  exact ⟨y,x,z,((col_symm S y x).trans hc).symm ▸ (some_mem_plus S _ _).mpr hcR,hxz,hyz⟩

end CCO.RealHull.Geometry
