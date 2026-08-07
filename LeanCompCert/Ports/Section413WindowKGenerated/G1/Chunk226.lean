import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk226

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362466162261652604, 362466169172256064⟩, ⟨405774800669481837, 405880411001123297⟩, true⟩

def state01 : KState := ⟨⟨362468282860671062, 362468289777619615⟩, ⟨357901230542357250, 358006984305174486⟩, true⟩

def words00 : List Nat := [371284128458130698, 371284128458909669, 371284128847025144, 371284129439474760, 371284129440026329, 371284129397563825, 371284127073377560, 371284125521791253, 371284123969961065, 371284123788424798]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 22600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 22600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488070900907441, 362488077824291207⟩, ⟨(-89545969378738698), (-89440070082519696)⟩, true⟩

def words01 : List Nat := [371284123088675537, 371284122383093326, 371284122924810928, 371284123199583485, 371284124070268461, 371284124941157591, 371284125399606840, 371284125400315301, 371284123797332037, 371284123972998934]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 22610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 22600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362452238619852382, 362452245549546951⟩, ⟨721274294846024239, 721380336925184881⟩, true⟩

def words02 : List Nat := [371284126101013879, 371284126101722333, 371284125628293160, 371284125149280833, 371284124766524748, 371284124767312798, 371284123906863362, 371284123539975660, 371284123172889826, 371284122718655444]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 22620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 22600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362504599244089047, 362504606180203998⟩, ⟨(-464088340458913173), (-463982153054611701)⟩, true⟩

def words03 : List Nat := [371284121310583312, 371284120452704874, 371284120027215123, 371284120027923918, 371284117862589678, 371284115393918663, 371284112925185152, 371284112406812807, 371284112268045254, 371284113174018114]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 22630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 22600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362454661359636154, 362454668302142378⟩, ⟨666713015170632419, 666819347305612907⟩, true⟩

def words04 : List Nat := [371284114074016118, 371284114074725003, 371284112629343089, 371284112881760056, 371284113241554902, 371284113242267274, 371284111917086024, 371284110587029817, 371284109256799918, 371284108449926291]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 22640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 22600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362428079123457348, 362428086072351465⟩, ⟨1269184144142272417, 1269290620995338263⟩, true⟩

def words05 : List Nat := [371284107798900924, 371284108447840561, 371284109089831522, 371284109090540855, 371284107532926419, 371284106246039030, 371284105342644192, 371284105343353409, 371284103134136652, 371284100662863175]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 22650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 22600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362467916906526498, 362467923861761464⟩, ⟨366280811025909611, 366387431596181337⟩, true⟩

def words06 : List Nat := [371284098191497095, 371284096527326664, 371284093897990127, 371284092968655199, 371284092039176233, 371284090799105082, 371284087954604781, 371284086533639002, 371284085635689443, 371284085636423846]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 22660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 22600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473037902616295, 362473044864344187⟩, ⟨250031592484294706, 250138360280205626⟩, true⟩

def words07 : List Nat := [371284084924080181, 371284083763175524, 371284082602081699, 371284081876678578, 371284080182044812, 371284079058791175, 371284077935404473, 371284076807376832, 371284074377976948, 371284073892575237]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 22670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 22600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362448469746944645, 362448476714993547⟩, ⟨807497106946111584, 807604018135843810⟩, true⟩

def words08 : List Nat := [371284074402544641, 371284074403259458, 371284073676344230, 371284072945312833, 371284072214083739, 371284071799284161, 371284070656121070, 371284070327743537, 371284069999151359, 371284069664228270]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 22680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 22600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362537721944455184, 362537728918917253⟩, ⟨(-1218112545166519512), (-1218005488429401628)⟩, true⟩

def words09 : List Nat := [371284068469092879, 371284068842877102, 371284070193204040, 371284070193926902, 371284069945266312, 371284069150307687, 371284069499948017, 371284069924364077, 371284072288679266, 371284074653095069]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 22690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 22600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 22600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk226
