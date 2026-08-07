import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk368

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362515429218855080, 362515448305167923⟩, ⟨(-1126360303834260823), (-1125885632805229887)⟩, true⟩

def state01 : KState := ⟨⟨362495266096225099, 362495285193362682⟩, ⟨(-384414195362958708), (-383939125927554136)⟩, true⟩

def words00 : List Nat := [371284855181263395, 371284855182462873, 371284855038794201, 371284855117337478, 371284855255604410, 371284855256833012, 371284854984261827, 371284854710229737, 371284854897879657, 371284855182606997]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 36800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 36800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362470227543936471, 362470246651878141⟩, ⟨537500252607427386, 537975719796168460⟩, true⟩

def words01 : List Nat := [371284856129236169, 371284857076290476, 371284857884176478, 371284857885376540, 371284857885174478, 371284857961744221, 371284858410347697, 371284858411548265, 371284858012038740, 371284857616565707]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 36810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 36800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484592360909610, 362484611479589909⟩, ⟨8641628724493034, 9117491363752700⟩, true⟩

def words02 : List Nat := [371284857560854811, 371284857670775284, 371284858307775622, 371284858945238327, 371284859467653346, 371284859468853588, 371284859008691753, 371284858853638873, 371284859034451968, 371284859035695360]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 36820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 36800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482943964702954, 362482963094320584⟩, ⟨69471813699383887, 69948079217012371⟩, true⟩

def words03 : List Nat := [371284859029871371, 371284859022507946, 371284859742404847, 371284860199939950, 371284860825464120, 371284861451402505, 371284862080696464, 371284862081897270, 371284861843583185, 371284861793539287]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 36830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 36800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480182047949095, 362480201188282465⟩, ⟨171197868274816352, 171674528614015894⟩, true⟩

def words04 : List Nat := [371284861887223032, 371284861888429656, 371284861380103317, 371284860870214187, 371284860359904058, 371284860073220677, 371284859644708168, 371284859799379621, 371284859925933627, 371284859927186509]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 36840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 36800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362511409974841952, 362511429126003197⟩, ⟨(-979669508022907877), (-979192448621701967)⟩, true⟩

def words05 : List Nat := [371284860277594815, 371284860755006782, 371284861875301109, 371284862014988459, 371284862041235437, 371284862067838530, 371284862829474803, 371284863225459526, 371284863947000755, 371284864669026401]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 36850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 36800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477499809080501, 362477518971094464⟩, ⟨270440085536195199, 270917545023504123⟩, true⟩

def words06 : List Nat := [371284865261512334, 371284865262734503, 371284865909875904, 371284866574568829, 371284867389908592, 371284867391110159, 371284867226101622, 371284867059300722, 371284866892040792, 371284866883896838]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 36860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 36800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463829199648172, 362463848372490104⟩, ⟨774668277850757332, 775146136620991776⟩, true⟩

def words07 : List Nat := [371284867221227445, 371284867758323659, 371284868192767303, 371284868193969290, 371284867746412599, 371284867438471771, 371284867555463922, 371284867556665970, 371284867003316739, 371284866434762908]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 36870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 36800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471828445645951, 362471847629258348⟩, ⟨479593520838935759, 480071776878353361⟩, true⟩

def words08 : List Nat := [371284865865693878, 371284865789399277, 371284865352675714, 371284865008438092, 371284864663855875, 371284864207508903, 371284862771417298, 371284862070579135, 371284861369145615, 371284861231233907]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 36880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 36800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489763739111070, 362489782933678209⟩, ⟨(-182099443998029158), (-181620783783974232)⟩, true⟩

def words09 : List Nat := [371284860879383048, 371284860532291347, 371284860498851777, 371284860648856176, 371284860959760064, 371284861271123801, 371284861425074244, 371284861426279824, 371284860959726904, 371284861094601112]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 36890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 36800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 36800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk368
