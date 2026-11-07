import CCO.UnfilteredEP.TemplateAge

/-! B064 C08: simultaneous singleton homogenization is a finite iteration
of ordinary Ramsey arrows. This module assumes no expansion property. -/

universe u v w z p q
namespace CCO.UnfilteredEP.FiniteAge.RamseyProvider

variable {OldSort : Type u} {Atom : Type v} {Label : Type p}
variable {K : FiniteAge.{u,v,w,z} OldSort Atom}
variable {T : FiniteTemplate OldSort Atom Label}
variable (P : K.RamseyProvider.{u,v,w,z,p,q} T)

/-- Peel ordinary arrows in reverse order. Passing to the selected
subcopy preserves every singleton homogeneity obtained earlier. -/
theorem simultaneous_singleton_list [Fintype Label] [Nonempty Label]
    (S : P.Singletons) (ramsey : P.Ramsey) (D : P.Obj) :
    ∀ labels : List Label, ∃ C : P.Obj,
      ∀ colour : ∀ t, P.Embedding (S.object t) C → Label,
        ∃ g : P.Embedding D C,
          ∀ t ∈ labels, ∀ f h : P.Embedding (S.object t) D,
            colour t (g.comp f) = colour t (g.comp h) := by
  intro labels
  induction labels with
  | nil =>
    refine ⟨D,?_⟩
    intro colour
    exact ⟨Embedding.id D,by simp⟩
  | cons t labels ih =>
    obtain ⟨E,hE⟩ := ih
    obtain ⟨C,hC⟩ := ramsey (S.object t) E (Fintype.card Label) (Fintype.card_pos)
    refine ⟨C,?_⟩
    intro colour
    let encode := Fintype.equivFin Label
    obtain ⟨g,hg⟩ := hC (fun f => encode (colour t f))
    obtain ⟨d,hd⟩ := hE (fun s f => colour s (g.comp f))
    refine ⟨g.comp d,?_⟩
    intro s hs f h
    rcases List.mem_cons.mp hs with hs | hs
    · subst s
      have he := encode.injective (hg (d.comp f) (d.comp h))
      simpa only [Embedding.comp_assoc] using he
    · have he := hd s hs f h
      simpa only [Embedding.comp_assoc] using he

/-- One fixed C works for every simultaneous labelling of the actual
singleton-embedding sets, separately constant on a single D-copy. -/
theorem simultaneous_singletons [Finite Label] [Nonempty Label]
    (S : P.Singletons) (ramsey : P.Ramsey) (D : P.Obj) :
    ∃ C : P.Obj,
      ∀ colour : ∀ t, P.Embedding (S.object t) C → Label,
        ∃ g : P.Embedding D C,
          ∀ t, ∀ f h : P.Embedding (S.object t) D,
            colour t (g.comp f) = colour t (g.comp h) := by
  classical
  let _ := Fintype.ofFinite Label
  obtain ⟨C,hC⟩ := P.simultaneous_singleton_list S ramsey D Finset.univ.toList
  exact ⟨C,fun colour => by
    obtain ⟨g,hg⟩ := hC colour
    exact ⟨g,fun t => hg t (by simp)⟩⟩

end CCO.UnfilteredEP.FiniteAge.RamseyProvider
