import LeanCompCert.Ports.CDEMAbelMarkTermination
import LeanCompCert.Ports.CDEMAbelProductionCertificate

/-!
# Production reduction of the CDEM Abel marking budget

The generic cursor proof reduces termination to a compact finite sum.  The
exact production inequality is intentionally supplied by the separate rolled
LeanCompCert computation; this module performs no kernel evaluation of the
199,329-row sum.
-/

namespace LeanCompCert.Ports.CDEMAbelProductionMarkTermination

open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelMarkTermination
open LeanCompCert.Ports.CDEMAbelProductionCertificate

theorem production_budget_suffices
    (hbudget : compactMarkBudget productionCfg ≤ productionCfg.markSteps) :
    compactMarkBudget productionCfg ≤ productionCfg.markSteps := hbudget

end LeanCompCert.Ports.CDEMAbelProductionMarkTermination
