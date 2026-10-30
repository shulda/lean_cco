import CCO.FullPhaseLift.Canonical.Expansion
import CCO.FullPhaseLift.BinarySource.FullAlignment

/-! Full homogeneity survives the ACTUAL finite definitional expansion.
This concerns the full language; no binary reduct homogeneity is inferred. -/

universe v
namespace CCO.FullPhaseLift.Canonical
noncomputable section

theorem expand_homogeneous {L : Signature} {M : Type v} (T : BoolTable L M)
    (hom : (toRelational T).Homogeneous) : (toRelational (expand T)).Homogeneous := by
  intro V _ B f g
  have heq : ∀ x y, f.point x = f.point y ↔ g.point x = g.point y :=
    fun x y => f.injective.eq_iff.trans g.injective.eq_iff.symm
  have hrel : ∀ {n} (R : L.language.Rel n) xs,
      (toRelational T).rel R (f.point ∘ xs) ↔
        (toRelational T).rel R (g.point ∘ xs) := by
    intro n R xs
    rcases R with ⟨r,hr⟩
    subst n
    have hf := f.rel_iff ⟨oldSymbol L r,oldSymbol_arity L r⟩ xs
    have hg := g.rel_iff ⟨oldSymbol L r,oldSymbol_arity L r⟩ xs
    have h := hf.trans hg.symm
    change (expand T (oldSymbol L r) ((f.point ∘ xs) ∘ Fin.cast (oldSymbol_arity L r)) = true) ↔
      (expand T (oldSymbol L r) ((g.point ∘ xs) ∘ Fin.cast (oldSymbol_arity L r)) = true) at h
    change T r (f.point ∘ xs) = true ↔ T r (g.point ∘ xs) = true
    simpa only [expand_old] using h
  obtain ⟨a,ha⟩ := BinarySource.full_tuple_homogeneous (toRelational T) hom
    f.point g.point heq hrel
  exact ⟨expandIso a,ha⟩

end
end CCO.FullPhaseLift.Canonical
