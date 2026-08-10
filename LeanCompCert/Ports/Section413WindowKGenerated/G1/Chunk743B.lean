import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk743A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk743B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk743A

def state06 : KState := ⟨⟨362493349552118277, 362493431999989386⟩, ⟨(-612026631917792324), (-607886368513720948)⟩, true⟩

def words05 : List Nat := [371285257284406848, 371285257164623556, 371285257101256480, 371285257103858987, 371285257044549933, 371285256956314490, 371285256956706915, 371285256974564403, 371285257086240432, 371285257199105674]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 74350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 74300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484524864948330, 362484607335893302⟩, ⟨44164772556929863, 48306751850412041⟩, true⟩

def words06 : List Nat := [371285257274514656, 371285257277071865, 371285257124495124, 371285257140679160, 371285257199546785, 371285257202109794, 371285257084240126, 371285256966428767, 371285256879186846, 371285256882106163]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 74360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 74300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469619316012644, 362469701809937579⟩, ⟨1152801950344861577, 1156945638778749313⟩, true⟩

def words07 : List Nat := [371285256959734771, 371285257047100936, 371285257131979562, 371285257134538415, 371285257009058492, 371285256863039929, 371285256747075120, 371285256749632934, 371285256542144812, 371285256335868996]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 74370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 74300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489848049234434, 362489930566090044⟩, ⟨(-351840604821216022), (-347695210687482906)⟩, true⟩

def words08 : List Nat := [371285256128484212, 371285256102791761, 371285256147147250, 371285256261527228, 371285256357629312, 371285256360199480, 371285256366131383, 371285256452171443, 371285256612497349, 371285256677976059]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 74380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 74300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481699284937824, 362481781825131317⟩, ⟨254422422679219220, 258569553031553244⟩, true⟩

def words09 : List Nat := [371285256739368211, 371285256801653141, 371285256956216074, 371285257022075463, 371285257142148012, 371285257263222268, 371285257383686698, 371285257386245085, 371285257265848271, 371285257222349484]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 74390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 74300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 74300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk743B
