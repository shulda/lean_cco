import CCO.TerminalHiddenHN.GenericCofinality
import CCO.TerminalHiddenHN.Irreducibility
import CCO.TerminalHiddenHN.ActualSAP
import CCO.TerminalHiddenHN.HNBinding
import CCO.TerminalHiddenHN.GeneralExport

/-! Public source anchors for B059. The standalone A02 cofinality and
readout exports retain their original scope: the latter consumes exactly
ordered hidden Ramsey. The standalone actual-signature irreducibility
export retains explicit NR2 and visible SAP, without infinite covers or
CCO. Terminal and general Ramsey exports discharge their hidden inputs
internally. The whole-age SAP/JEP and all-orders HN exports are separately
public before readout, for later source consumers. -/

namespace CCO.TerminalHiddenHN.Source

export RealInterpretation
  (real_root_closure_cofinal hasFiniteRelationalRamseyExpansion_of_hiddenRamsey)

export CCO.TerminalHiddenHN
  (original_hidden_irreducible_of_embedding
    terminal_finite_relational_ramsey_expansion
    general_finite_relational_ramsey_expansion
    actual_hidden_age_sap actual_hidden_age_jep
    actual_hidden_uniform_local_finiteness actual_hidden_ordered_ramsey)

end CCO.TerminalHiddenHN.Source
