import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk789A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk789B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk789A

def state06 : KState := ⟨⟨362484358689392006, 362484452085854961⟩, ⟨54781697371586827, 59761551362028023⟩, true⟩

def words05 : List Nat := [371285209204605884, 371285209162550898, 371285209141021294, 371285209144025991, 371285209087367953, 371285209081037023, 371285209073830795, 371285209071826551, 371285208950516668, 371285208944408179]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 78950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 78900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473338909061826, 362473432329792501⟩, ⟨925014055911184520, 929995826208312782⟩, true⟩

def words06 : List Nat := [371285209082265096, 371285209085005021, 371285209079216118, 371285209074351637, 371285209072656219, 371285209075691047, 371285209012300576, 371285208985659807, 371285208958088126, 371285208900974068]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 78960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 78900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362503510221522192, 362503603666871126⟩, ⟨(-1457765873083409750), (-1452782158556313856)⟩, true⟩

def words07 : List Nat := [371285208753698560, 371285208753837613, 371285208893331915, 371285208903662878, 371285208905808253, 371285208901517475, 371285209048966208, 371285209124698124, 371285209359449190, 371285209595403858]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 78970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 78900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362498617955036648, 362498711425022489⟩, ⟨(-1071393181745699277), (-1066407521271550347)⟩, true⟩

def words08 : List Nat := [371285209799035401, 371285209875509599, 371285210069842343, 371285210265635904, 371285210509302572, 371285210563460719, 371285210616536192, 371285210670575555, 371285210883598340, 371285211057622766]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 78980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 78900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479121944058454, 362479215438599536⟩, ⟨468725053947539889, 473712654164717643⟩, true⟩

def words09 : List Nat := [371285211284778227, 371285211513061041, 371285211727308173, 371285211746200879, 371285211755304522, 371285211765695812, 371285211925191461, 371285211927919924, 371285211874120056, 371285211801310482]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 78990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 78900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 78900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk789B
