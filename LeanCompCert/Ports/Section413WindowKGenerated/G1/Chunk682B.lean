import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk682A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk682B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk682A

def state06 : KState := ⟨⟨362468815661686552, 362468884675348789⟩, ⟨1127897953242455817, 1131079593671342301⟩, true⟩

def words05 : List Nat := [371285454749340439, 371285455030002896, 371285455310073398, 371285455312405898, 371285455306391044, 371285455276162203, 371285455304493617, 371285455306826241, 371285455082420571, 371285454842264572]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 68250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 68200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484558454940012, 362484627489472918⟩, ⟨53247926147454535, 56430991314653865⟩, true⟩

def words06 : List Nat := [371285454601099602, 371285454575323398, 371285454455072471, 371285454433124658, 371285454410400276, 371285454324553656, 371285454093596760, 371285454021368510, 371285454072546460, 371285454074961635]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 68260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 68200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490658825485588, 362490727881327482⟩, ⟨(-363267126657691955), (-360082606617763827)⟩, true⟩

def words07 : List Nat := [371285454064628695, 371285454010669866, 371285454080700384, 371285454101175094, 371285454186835729, 371285454273376572, 371285454316717383, 371285454319091450, 371285454260861838, 371285454341007075]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 68270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 68200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480788316776230, 362480857393394811⟩, ⟨310775206472871802, 313961145252719172⟩, true⟩

def words08 : List Nat := [371285454634096287, 371285454642164910, 371285454649520892, 371285454657626301, 371285454673863874, 371285454676440682, 371285454698557973, 371285454788781255, 371285454859792163, 371285454862208001]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 68280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 68200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489854371204813, 362489923468908052⟩, ⟨(-308348516480268595), (-305161137721159431)⟩, true⟩

def words09 : List Nat := [371285454908757266, 371285455023882811, 371285455315559782, 371285455322327351, 371285455324135068, 371285455288920172, 371285455402173137, 371285455447029526, 371285455514069005, 371285455582087638]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 68290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 68200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 68200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk682B
