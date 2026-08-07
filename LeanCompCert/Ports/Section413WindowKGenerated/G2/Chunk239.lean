import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk239

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360672713320061305, 360672716688326941⟩, ⟨(-2164292823160471015), (-2164238361223078785)⟩, true⟩

def state01 : KState := ⟨⟨360631851235941417, 360631854607169347⟩, ⟨(-1187814583992083841), (-1187760051241127935)⟩, true⟩

def words00 : List Nat := [360582169351134037, 360582172705964633, 360582175578055081, 360582178449997348, 360582180137649221, 360582180137960447, 360582180088075221, 360582178915771623, 360582178318598972, 360582180396503080]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 23900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 23900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595260701134174, 360595264075297972⟩, ⟨(-312429904921061285), (-312375301958628889)⟩, true⟩

def words01 : List Nat := [360582184221495973, 360582188046233796, 360582190978650176, 360582193665715818, 360582195900428117, 360582198135035670, 360582202115878544, 360582204360574097, 360582204906831781, 360582205453084912]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 23910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 23900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360701372877228094, 360701376254330439⟩, ⟨(-2851249861601448466), (-2851195188334263828)⟩, true⟩

def words02 : List Nat := [360582206738123603, 360582208922144265, 360582212252085200, 360582215581807106, 360582217175496149, 360582218815708117, 360582221609710504, 360582224403570205, 360582228941499404, 360582233920607057]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 23920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 23900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360628579774241406, 360628583154318596⟩, ⟨(-1108965848492465320), (-1108911104022940268)⟩, true⟩

def words03 : List Nat := [360582238009678192, 360582242098439262, 360582245427525762, 360582249633203066, 360582253387537781, 360582257141612388, 360582259831353887, 360582260788354988, 360582262723543265, 360582264658682535]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 23930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 23900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572719616221580, 360572722999232662⟩, ⟨228587430555945380, 228642245277731378⟩, true⟩

def words04 : List Nat := [360582267810512905, 360582269229877242, 360582269493392690, 360582269756919870, 360582269757180941, 360582270509629869, 360582270514644926, 360582270519713049, 360582270519993717, 360582269648304802]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 23940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 23900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360657598725150794, 360657602111106310⟩, ⟨(-1804686086450691168), (-1804631201195290906)⟩, true⟩

def words05 : List Nat := [360582269890299434, 360582270530922277, 360582271715848238, 360582273691591101, 360582274186856735, 360582274682105503, 360582276917447178, 360582280469342471, 360582283613237815, 360582286756939319]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360602668356587792, 360602671745517026⟩, ⟨(-488656096285385364), (-488601139764951064)⟩, true⟩

def words06 : List Nat := [360582288481019209, 360582288481331220, 360582289484580624, 360582290494289903, 360582291055047976, 360582291055360461, 360582290864714022, 360582289788444106, 360582288712200855, 360582288735222715]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360550024478279558, 360550027870147779⟩, ⟨773606630730152853, 773661657712800993⟩, true⟩

def words07 : List Nat := [360582291323798692, 360582293912219703, 360582295422494041, 360582295422806232, 360582295204722733, 360582293715221366, 360582292473570389, 360582292473883246, 360582292003344149, 360582290658209197]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584931833052132, 360584935227870032⟩, ⟨(-63318201530937038), (-63263103800449532)⟩, true⟩

def words08 : List Nat := [360582289704755946, 360582291461915352, 360582294116955737, 360582296771834114, 360582297843564921, 360582297843877268, 360582298154127399, 360582298494614175, 360582298494871600, 360582298276354862]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360609122682182560, 360609126079974937⟩, ⟨(-643846487071809777), (-643791317968820743)⟩, true⟩

def words09 : List Nat := [360582298276635052, 360582297064309095, 360582296374954206, 360582297993186313, 360582299164345739, 360582300335463754, 360582300433787107, 360582300434101067, 360582301441369906, 360582302559372928]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk239
