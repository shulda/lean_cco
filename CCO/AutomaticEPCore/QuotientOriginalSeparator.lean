import CCO.AutomaticEPCore.QuotientCanonicalSeparator
import CCO.AutomaticEPCore.SourceQuotientLift

/-! The canonical quotient edge obtained from actual lower-rank tower
induction is lifted back to an ORIGINAL bipartite atom at PRECISELY
the two requested old terminal types. The actual E-occupancy
representative sorts and source-supported class theorem discharge the
source-side endpoints; no quotient SAP or section is assumed. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.ParityHasse.Original
noncomputable section

/-- C25 final receiving bridge for two actual selected points. Their
source quotient sort names are the true original E-occupancies of s,t.
Every E-class has a source representative at its canonical parent;
actual occupancy supplies both requested terminal types. -/
theorem selected_quotient_edge_original_separator
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (b : (originalCoreQuotient A base hOne E).Atom base base)
    (bip : (atomGraph (originalCoreQuotient A base hOne E) b).IsBipartite)
    (s t : B.Sorts)
    (x : (originalExactSelectedQuotientCurrentSource A B P transport
      base hOne E).Point (Quotient.mk'' s))
    (y : (originalExactSelectedQuotientCurrentSource A B P transport
      base hOne E).Point (Quotient.mk'' t))
    (edge : (originalCoreQuotient A base hOne E).atomRel b
      (selectedOriginalClassEquiv A B P transport base hOne E ⟨Quotient.mk'' s,x⟩)
      (selectedOriginalClassEquiv A B P transport base hOne E ⟨Quotient.mk'' t,y⟩)) :
    ∃ a : A.source.Atom base base,
      (atomGraph A.source a).IsBipartite ∧
      originalAtomTable A B P base hOne a s t := by
  let cs : OriginalOccupancy A B P base hOne E := Quotient.mk'' s
  let ct : OriginalOccupancy A B P base hOne E := Quotient.mk'' t
  let ps : B.Sorts := originalOccupancyRepresentative A B P base hOne E cs
  let pt : B.Sorts := originalOccupancyRepresentative A B P base hOne E ct
  have hs : prefixSupport P (originalExactGlobalRelation A base hOne E) ps s := by
    have h : (Quotient.mk'' ps : OriginalOccupancy A B P base hOne E) =
        (Quotient.mk'' s : OriginalOccupancy A B P base hOne E) :=
      originalOccupancyRepresentative_class A B P base hOne E cs
    exact Quotient.exact h
  have ht : prefixSupport P (originalExactGlobalRelation A base hOne E) pt t := by
    have h : (Quotient.mk'' pt : OriginalOccupancy A B P base hOne E) =
        (Quotient.mk'' t : OriginalOccupancy A B P base hOne E) :=
      originalOccupancyRepresentative_class A B P base hOne E ct
    exact Quotient.exact h
  have canonicalEdge :
      (atomGraph (originalCoreQuotient A base hOne E) b).Adj
        (Quotient.mk'' (originalPointEquiv A base hOne
          (P.project ⟨ps,Quotient.out x⟩)))
        (Quotient.mk'' (originalPointEquiv A base hOne
          (P.project ⟨pt,Quotient.out y⟩))) := by
    have he := edge
    rw [selectedOriginalClassEquiv_apply A B P transport base hOne E
        (⟨cs,x⟩ : Sigma
          (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).Point),
      selectedOriginalClassEquiv_apply A B P transport base hOne E
        (⟨ct,y⟩ : Sigma
          (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).Point)] at he
    change (atomGraph (originalCoreQuotient A base hOne E) b).Adj
      (Quotient.mk'' (originalPointEquiv A base hOne
        (P.project ⟨ps,Quotient.out x⟩)))
      (Quotient.mk'' (originalPointEquiv A base hOne
        (P.project ⟨pt,Quotient.out y⟩))) at he
    exact he
  exact original_quotient_bipartite_separator_lift A B P base hOne E b bip
    ps pt s t (Quotient.out x) (Quotient.out y) hs ht canonicalEdge

/-- The actual smaller ORIGINAL-rank tower hypothesis yields an
ORIGINAL bipartite source atom at the exact requested final names,
after complete canonical colour/code transport and the genuine C25
E-class occupancy lift. No conclusion of the outer strong induction
is used as an extra source/provider hypothesis. -/
theorem actual_quotient_rank_step_original_separator
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base)
    {next : CertifiedGateTower.ExactPrefix A}
    (history : History IsoGateTower.Step (CertifiedGateTower.initial A) next)
    (terminal : next.current.Terminal)
    (s t : next.current.Sorts)
    (different : ¬prefixSupport next.reduct
      (originalExactGlobalRelation A base hOne E) s t)
    (smaller :
      let Q := originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)
      ActualTowerSeparation Q.current (Quotient.mk'' base)
        (original_initial_selected_quotient_one_sort A base hOne E)) :
    ∃ a : A.source.Atom base base, (atomGraph A.source a).IsBipartite ∧
      originalAtomTable A next.current next.reduct base hOne a s t := by
  obtain ⟨b,bip,p,q,hps,hqt,hedge⟩ :=
    actual_quotient_rank_step_canonical_edge A base hOne E
      history terminal s t different smaller
  rcases p with ⟨ps,x⟩
  rcases q with ⟨pt,y⟩
  dsimp only [Sigma.fst] at hps hqt
  subst ps
  subst pt
  exact selected_quotient_edge_original_separator A next.current next.reduct
    next.transport base hOne E b bip s t x y hedge

end
end CCO.AutomaticEPCore
