import CCO.CloneSAP.Quotient
import CCO.RawExact.Presentations

universe u v w
namespace CCO.CloneSAP
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

/-- The positive word consists of two actual clone diversity edges. -/
def kernelWord (i : ι) : RawWord (source S) i i :=
  .atom (.inr ⟨rfl⟩) (.atom (.inr ⟨rfl⟩) (.nil i))

/-- C23--C25: the actual FULL RAW profile is K, including the real diagonal. -/
theorem kernelWord_relation (i : ι) :
    RawWord.relation (source S) (kernelWord S i) = (kernelSetoid (X := X) i).r := by
  have hc : (source S).atomRel (.inr ⟨rfl⟩ : (source S).Atom i i) = cloneRel := by
    funext x y
    exact propext (source_clone_iff S x y)
  change TRel.comp ((source S).atomRel (.inr ⟨rfl⟩))
    (TRel.comp ((source S).atomRel (.inr ⟨rfl⟩)) (TRel.ident (Carrier X) i)) = _
  rw [TRel.comp_ident,hc,clone_comp_eq_kernel]
  rfl

/-- A singleton finite RAW presentation witnesses exactness and real inhabitance. -/
noncomputable def kernelExact (i : ι) : RawExact.NonemptyExact (source S) i i where
  words := [kernelWord S i]
  nonempty := by
    obtain ⟨q⟩ := S.nonemptySort i
    refine ⟨(q,0),(q,0),?_⟩
    intro word hw
    have he : word = kernelWord S i := by simpa only [List.mem_singleton] using hw
    rw [he,kernelWord_relation]
    rfl

/-- Exactness is proved by a genuine finite word presentation; no generic
exact-quotient pullback or later source theorem is assumed. -/
theorem kernelExact_relation (i : ι) :
    RawExact.evaluate (source S) (kernelExact S i).words = (kernelSetoid (X := X) i).r := by
  funext x y
  apply propext
  constructor
  · intro h
    exact (kernelWord_relation S i) ▸ h (kernelWord S i) (by simp [kernelExact])
  · intro h word hw
    have he : word = kernelWord S i := by simpa only [kernelExact,List.mem_singleton] using hw
    rw [he,kernelWord_relation]
    exact h

end CCO.CloneSAP
