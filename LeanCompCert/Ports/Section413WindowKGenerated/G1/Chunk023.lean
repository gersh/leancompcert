import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk023

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362864845958026726, 362864846015471728⟩, ⟨(-918699779969040415), (-918699690292239425)⟩, true⟩

def state01 : KState := ⟨⟨362338425910703841, 362338425968677528⟩, ⟨292291528772101422, 292291619667583428⟩, true⟩

def words00 : List Nat := [371265744865432740, 371265744865491201, 371265655546685847, 371265630823959725, 371265638156819236, 371265638156877750, 371265422030388226, 371265205662648280, 371264989482297974, 371264959137364794]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 2300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 2300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362264032244306228, 362264032302810716⟩, ⟨466727627256080904, 466727719380474976⟩, true⟩

def words01 : List Nat := [371265035222849001, 371265165947785725, 371265293793907376, 371265293793966551, 371265273297557677, 371265291323687468, 371265380917687209, 371265380917746410, 371265294794930281, 371265208043922990]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 2310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 2300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362173450329878283, 362173450388912657⟩, ⟨678482871640543696, 678482964996996578⟩, true⟩

def words02 : List Nat := [371265123967171618, 371265123967237203, 371265073058101020, 371265104354830294, 371265116517900593, 371265116517959837, 371264885108465988, 371264769445888677, 371264653882604818, 371264644794490768]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 2320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 2300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362441875232308293, 362441875291885053⟩, ⟨51312887611486418, 51312982234449308⟩, true⟩

def words03 : List Nat := [371264519872011506, 371264346768625033, 371264182428059566, 371264182428124843, 371264099995628338, 371264074468235948, 371264048962669418, 371264003625448550, 371263813291911702, 371263803916771570]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 2330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 2300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362226146770916941, 362226146831025838⟩, ⟨557591723980287225, 557591819851256583⟩, true⟩

def words04 : List Nat := [371263965833191743, 371263965833251412, 371263896619854424, 371263789180001674, 371263681831759836, 371263574957294265, 371263413810967751, 371263423261658150, 371263423261703577, 371263419945856160]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 2340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 2300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362863376566286955, 362863376626940080⟩, ⟨(-942096161269897548), (-942096064117274392)⟩, true⟩

def words05 : List Nat := [371263397643850655, 371263476199386525, 371263668857816997, 371263709503338851, 371263717791830879, 371263726073307966, 371263913095362335, 371264014157938053, 371264183379364931, 371264352457470672]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 2350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 2300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362464258705379427, 362464258766576314⟩, ⟨313636350118487, 313734788849479⟩, true⟩

def words06 : List Nat := [371264520360362251, 371264520360422470, 371264489079545926, 371264526558380187, 371264563196619642, 371264563196681221, 371264493490188747, 371264421416245932, 371264391144055737, 371264391144124352]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 2360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 2300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362347207289623893, 362347207351367144⟩, ⟨279746369397966775, 279746469134339677⟩, true⟩

def words07 : List Nat := [371264567249238024, 371264743261736237, 371264889291211499, 371264889291272103, 371264800978976921, 371264754645199703, 371264837569653219, 371264837569713957, 371264797292086292, 371264747884616867]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 2370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 2300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362564168042239087, 362564168104526890⟩, ⟨(-235725669614139257), (-235725568578872227)⟩, true⟩

def words08 : List Nat := [371264824423279220, 371264864426875746, 371265079553597364, 371265294499944338, 371265482108476578, 371265482108537531, 371265437327560516, 371265412770582523, 371265538159451638, 371265579410014606]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 2380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 2300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362993639764978889, 362993639827825145⟩, ⟨(-1264120136103536840), (-1264120033730779670)⟩, true⟩

def words09 : List Nat := [371265618745130988, 371265658047393472, 371265871292975713, 371266035143725466, 371266251010026795, 371266466696236998, 371266657314660989, 371266703590220189, 371266923147027663, 371267142520981839]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 2390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 2300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 2300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk023
