import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk910A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk910B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk910A

def state06 : KState := ⟨⟨362472036301884857, 362472161886983817⟩, ⟨1171479801389279801, 1179200997207195319⟩, true⟩

def words05 : List Nat := [371285112125294923, 371285112161781804, 371285112184346672, 371285112187527463, 371285112066536490, 371285111984134943, 371285111899979817, 371285111874468458, 371285111740093030, 371285111601427121]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470154978135770, 362470280591717968⟩, ⟨1342836608008123129, 1350560397659628787⟩, true⟩

def words06 : List Nat := [371285111461375225, 371285111413719542, 371285111304362843, 371285111246599045, 371285111187829452, 371285111121422307, 371285110893333337, 371285110755282984, 371285110615640995, 371285110507141924]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478401722904624, 362478527365524931⟩, ⟨591760081496032262, 599486515787587110⟩, true⟩

def words07 : List Nat := [371285110346704719, 371285110186414006, 371285110024786490, 371285109967010083, 371285109853595513, 371285109777976412, 371285109701354737, 371285109601865870, 371285109411306671, 371285109343080790]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476278294862575, 362476403965788039⟩, ⟨785190178716196346, 792919191189934052⟩, true⟩

def words08 : List Nat := [371285109321151801, 371285109324332947, 371285109214278238, 371285109095118391, 371285108974711316, 371285108892495166, 371285108778326933, 371285108774557000, 371285108769695151, 371285108754361867]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489475396725456, 362489601096399527⟩, ⟨(-417048785629820444), (-409317154298554668)⟩, true⟩

def words09 : List Nat := [371285108661021820, 371285108571931934, 371285108493326025, 371285108496509492, 371285108371066523, 371285108227363607, 371285108082339284, 371285108059167128, 371285108039565084, 371285108092433615]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk910B
