import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk143

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569715841528582, 360569716992509182⟩, ⟨157255315340084319, 157266461139597303⟩, true⟩

def state01 : KState := ⟨⟨360521127470303504, 360521128622982556⟩, ⟨851680558386754625, 851691728482435943⟩, true⟩

def words00 : List Nat := [360580713878284235, 360580709152111809, 360580699570052377, 360580694845354268, 360580690121270036, 360580684177066680, 360580676249155129, 360580665245190163, 360580654242726483, 360580645864665466]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 14300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 14300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360344802907592543, 360344804061949522⟩, ⟨3376008745004043800, 3376019939119425634⟩, true⟩

def words01 : List Nat := [360580641705965051, 360580638246329350, 360580634787158518, 360580628169556187, 360580620145568044, 360580608697413488, 360580597250806544, 360580589101381930, 360580576108634254, 360580559644290265]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 14310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 14300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569332989166062, 360569334145210310⟩, ⟨160072263488292812, 160083481773562972⟩, true⟩

def words02 : List Nat := [360580543182205735, 360580531565856652, 360580524268352523, 360580521814609480, 360580519361195270, 360580512758684959, 360580507766594731, 360580507615939682, 360580507465254794, 360580505358174272]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 14320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 14300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360469200994676430, 360469202152420234⟩, ⟨1595451820401414975, 1595463063049919245⟩, true⟩

def words03 : List Nat := [360580504578819966, 360580500415217877, 360580496252163841, 360580492790420005, 360580491767892745, 360580488378084368, 360580484988728128, 360580478697556943, 360580469539276770, 360580461780247983]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 14330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 14300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360538996155448368, 360538997314877649⟩, ⟨593971297072781060, 593982563899466720⟩, true⟩

def words04 : List Nat := [360580454022242808, 360580451097606286, 360580445499612245, 360580436202115580, 360580426905885379, 360580415073591872, 360580405749743700, 360580401257095531, 360580396765053725, 360580389828041375]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 14340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 14300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360569997053578147, 360569998214694721⟩, ⟨148870200486425074, 148881491534146800⟩, true⟩

def words05 : List Nat := [360580387487838082, 360580388031906661, 360580391384360585, 360580391384539437, 360580389919438884, 360580383633208452, 360580377347822178, 360580370823376605, 360580366728440663, 360580366006584286]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 14350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 14300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360572114272184169, 360572115435005034⟩, ⟨117800333153349175, 117811648682945183⟩, true⟩

def words06 : List Nat := [360580365284802986, 360580362123990061, 360580356343932705, 360580353627715128, 360580350911824175, 360580344525085283, 360580337485021665, 360580328011359735, 360580318538982484, 360580313879589791]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 14360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 14300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360438203959499848, 360438205124008314⟩, ⟨2042631648342650389, 2042642988131732009⟩, true⟩

def words07 : List Nat := [360580313309251921, 360580312565770304, 360580311822374182, 360580308642080661, 360580300659850935, 360580290186105555, 360580279713766219, 360580269948396856, 360580262498336768, 360580252619705931]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 14370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 14300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587290184125861, 360587291350325211⟩, ⟨(-102009890092324913), (-101998525979943147)⟩, true⟩

def words08 : List Nat := [360580242742408876, 360580236208371039, 360580233217183864, 360580232241568881, 360580231266078096, 360580225650355540, 360580215238615236, 360580209625254891, 360580204012621522, 360580203689566408]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 14380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 14300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360475788188912450, 360475789356823185⟩, ⟨1503342513123123131, 1503353901870893143⟩, true⟩

def words09 : List Nat := [360580203689728615, 360580200729097973, 360580197768841794, 360580199515682020, 360580200390784669, 360580201265794926, 360580201265954807, 360580199721621433, 360580196183609979, 360580188933341998]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 14390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 14300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 14300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk143
