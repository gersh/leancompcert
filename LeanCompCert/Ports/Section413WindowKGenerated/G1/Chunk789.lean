import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk789

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476780417093158, 362476873666157548⟩, ⟨653106617087490624, 658074836889384100⟩, true⟩

def state01 : KState := ⟨⟨362469187600761559, 362469280874076163⟩, ⟨1252230683533000339, 1257200816805090765⟩, true⟩

def words00 : List Nat := [371285214236075290, 371285214238800028, 371285214081656890, 371285213893677959, 371285213704584496, 371285213551472237, 371285213316927868, 371285213202255608, 371285213086692457, 371285212958942531]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 78900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 78900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489673814489393, 362489767112503050⟩, ⟨(-364472987567047242), (-359500905170352602)⟩, true⟩

def words01 : List Nat := [371285212758923620, 371285212627057101, 371285212493712748, 371285212446835251, 371285212293860376, 371285212115711651, 371285211936483158, 371285211895280746, 371285211852127861, 371285211912934237]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 78910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 78900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476051292884175, 362476144615489422⟩, ⟨710619819750346692, 715593843042551204⟩, true⟩

def words02 : List Nat := [371285211957729371, 371285211960454949, 371285211791132339, 371285211729074837, 371285211665750374, 371285211562755838, 371285211331187000, 371285211100563315, 371285210868800133, 371285210798728274]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 78920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 78900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362468406946195044, 362468500293354506⟩, ⟨1314069190376427571, 1319045151855781695⟩, true⟩

def words03 : List Nat := [371285210685719869, 371285210675406059, 371285210664145708, 371285210654218204, 371285210451945122, 371285210300366508, 371285210147311064, 371285210144561008, 371285209966799843, 371285209758161395]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 78930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 78900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481559876117059, 362481653247687774⟩, ⟨275768305109852126, 280746193736248586⟩, true⟩

def words04 : List Nat := [371285209548339958, 371285209500027634, 371285209391296874, 371285209409551354, 371285209412229966, 371285209415003939, 371285209284169412, 371285209237232454, 371285209244782475, 371285209247608436]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 78940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 78900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk789
