import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk726A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk726B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk726A

def state06 : KState := ⟨⟨362480469851492550, 362480548431183587⟩, ⟨339788820659990003, 343644720236174481⟩, true⟩

def words05 : List Nat := [371285278297771692, 371285278307380158, 371285278363820715, 371285278366569399, 371285278328021001, 371285278298526650, 371285278268183439, 371285278223199614, 371285277982841284, 371285277920864790]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 72650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 72600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477674667356410, 362477753269247897⟩, ⟨542927463055242750, 546784975831784556⟩, true⟩

def words06 : List Nat := [371285277981560727, 371285277984056415, 371285277892840774, 371285277799959383, 371285277706100530, 371285277670642146, 371285277567339696, 371285277540965736, 371285277513771187, 371285277487987842]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 72660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 72600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507554990163552, 362507633614624832⟩, ⟨(-1628601517796700915), (-1624742364759994049)⟩, true⟩

def words07 : List Nat := [371285277471740460, 371285277560358713, 371285277836773307, 371285277992346953, 371285278109826110, 371285278228026514, 371285278443187827, 371285278564425042, 371285278873699284, 371285279184102963]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 72670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 72600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491600095280630, 362491678742285381⟩, ⟨(-468989298616404190), (-465128507005023322)⟩, true⟩

def words08 : List Nat := [371285279454089639, 371285279472497938, 371285279615065549, 371285279758918056, 371285279958878218, 371285279961373696, 371285279909307017, 371285279858861252, 371285279943084475, 371285280033958284]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 72680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 72600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482472303601456, 362482550973036076⟩, ⟨194625125306069900, 198487547458905998⟩, true⟩

def words09 : List Nat := [371285280296676734, 371285280560388243, 371285280813698560, 371285280871410282, 371285280932433683, 371285280994693902, 371285281229951197, 371285281233542112, 371285281235420560, 371285281200648991]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 72690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 72600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 72600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk726B
