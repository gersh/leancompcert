import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk430

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576764702925731, 360576776159595900⟩, ⟨267105492154392689, 267438417837709741⟩, true⟩

def state01 : KState := ⟨⟨360616339358242918, 360616350820457454⟩, ⟨(-1434898009433325950), (-1434564845314925838)⟩, true⟩

def words00 : List Nat := [360582995513531335, 360582995466631843, 360582996119753091, 360582996772958908, 360582996935143414, 360582996935729823, 360582996559816653, 360582996469239513, 360582996603491609, 360582997379586167]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 43000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 43000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360616556269002138, 360616567736799869⟩, ⟨(-1444238020133670953), (-1443904615854397433)⟩, true⟩

def words01 : List Nat := [360582997833065776, 360582998286582828, 360582999280606477, 360583000610244312, 360583001568432582, 360583002526664751, 360583003149044262, 360583003389295398, 360583004169973096, 360583004950815016]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 43010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 43000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360622192439992120, 360622203913321355⟩, ⟨(-1686767705600597079), (-1686434063328301903)⟩, true⟩

def words02 : List Nat := [360583005812169746, 360583006703677559, 360583007322824054, 360583007942005813, 360583008424570160, 360583009252378373, 360583010258357035, 360583011264400419, 360583011859182843, 360583012770579418]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 43020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 43000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360655942026406803, 360655953505273017⟩, ⟨(-3139283086622541288), (-3138949206066860640)⟩, true⟩

def words03 : List Nat := [360583013988547584, 360583015206635112, 360583016672420420, 360583017600847069, 360583018069434795, 360583018538056188, 360583019546527027, 360583020833681252, 360583022528688191, 360583024223749195]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 43030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 43000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360607300855079556, 360607312339542568⟩, ⟨(-1045844404478379146), (-1045510283009483730)⟩, true⟩

def words04 : List Nat := [360583025646866625, 360583026532729368, 360583026957439944, 360583027382290580, 360583027667806296, 360583027668393367, 360583027416729421, 360583026893387581, 360583026385713083, 360583026950515380]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 43040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 43000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360580376352703933, 360580387842694561⟩, ⟨113586736652035333, 113921096112513829⟩, true⟩

def words05 : List Nat := [360583028054694964, 360583029158935781, 360583029971024959, 360583030961283566, 360583031747205898, 360583032533256946, 360583033304710942, 360583033539236398, 360583033539760010, 360583033478925693]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360623528360452205, 360623539855984471⟩, ⟨(-1744769038323056536), (-1744434440212589182)⟩, true⟩

def words06 : List Nat := [360583033475383083, 360583033803566342, 360583034670932418, 360583035538380700, 360583035870012554, 360583035870599968, 360583036361854985, 360583036877516396, 360583037546571845, 360583038487541375]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360630082674125975, 360630094175258629⟩, ⟨(-2027183800880704521), (-2026848961533810139)⟩, true⟩

def words07 : List Nat := [360583039019391486, 360583039551271838, 360583040314787863, 360583041348308275, 360583042245992103, 360583043143733455, 360583043746842716, 360583044591682487, 360583045684302661, 360583046777066066]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360626991716017840, 360627003222677621⟩, ⟨(-1894010182722258624), (-1893675105238514462)⟩, true⟩

def words08 : List Nat := [360583048244922133, 360583049555272872, 360583050594471369, 360583051633680898, 360583052303311171, 360583053306555904, 360583054390640704, 360583055474784472, 360583056248171573, 360583057268644563]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360658158493787587, 360658170006006111⟩, ⟨(-3237115110081850611), (-3236779793045585743)⟩, true⟩

def words09 : List Nat := [360583058605020179, 360583059941524980, 360583061816357891, 360583063409361024, 360583064509876006, 360583065610381802, 360583067083954209, 360583068963287265, 360583070706254495, 360583072449266231]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk430
