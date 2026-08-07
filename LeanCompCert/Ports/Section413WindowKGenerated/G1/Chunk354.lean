import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk354

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486869132521966, 362486886737968563⟩, ⟨(-67116187187344206), (-66694982946314640)⟩, true⟩

def state01 : KState := ⟨⟨362479685652299054, 362479703267981353⟩, ⟨187312845040987929, 187734411679756619⟩, true⟩

def words00 : List Nat := [371285003604013754, 371285003605164436, 371285003562800773, 371285003516119146, 371285003569120608, 371285003570420833, 371285004017695801, 371285004641025817, 371285005001094394, 371285005002284651]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 35400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 35400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362505446773221464, 362505464399300712⟩, ⟨(-725081496106652999), (-724659561260015423)⟩, true⟩

def words01 : List Nat := [371285005201043931, 371285005550090103, 371285006228671926, 371285006229822204, 371285005846154607, 371285005328832383, 371285004987471275, 371285004988738210, 371285005347697417, 371285005926607677]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 35410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 35400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479492607737366, 362479510244187929⟩, ⟨194286474124719908, 194708776375568090⟩, true⟩

def words02 : List Nat := [371285006500528610, 371285006501679363, 371285006545128230, 371285006966320453, 371285007550115011, 371285007551265713, 371285007073486112, 371285006430209854, 371285005833516257, 371285005834827940]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 35420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 35400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485623753490233, 362485641400307394⟩, ⟨(-22938015639712588), (-22515346046904904)⟩, true⟩

def words03 : List Nat := [371285005928106344, 371285006176950781, 371285006415297742, 371285006416468619, 371285005994463594, 371285005747534670, 371285006048043484, 371285006071350758, 371285006090138059, 371285006109371842]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 35430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 35400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362501891059589998, 362501908716723355⟩, ⟨(-599540562166700419), (-599117526915708733)⟩, true⟩

def words04 : List Nat := [371285006384767841, 371285006393564972, 371285006886163599, 371285007379190769, 371285007667319984, 371285007668472070, 371285007218782910, 371285007392890348, 371285008362161632, 371285008840079094]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 35440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 35400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488077636104068, 362488095303716505⟩, ⟨(-109746827967445255), (-109323421179811367)⟩, true⟩

def words05 : List Nat := [371285009273944671, 371285009708151070, 371285010553639811, 371285011093696230, 371285011663746651, 371285012234208038, 371285012750741405, 371285012751893214, 371285012295489670, 371285012383855819]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 35450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 35400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486838378376445, 362486856056261211⟩, ⟨(-65652866309530365), (-65229095212350193)⟩, true⟩

def words06 : List Nat := [371285013266853097, 371285013646609904, 371285014021845849, 371285014397474940, 371285014880328584, 371285015029139841, 371285015765317088, 371285016501910046, 371285017061688005, 371285017114725525]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 35460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 35400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362509893701142693, 362509911389455858⟩, ⟨(-883505775379559154), (-883081634334890438)⟩, true⟩

def words07 : List Nat := [371285017879364452, 371285018644571532, 371285019988984195, 371285020274955898, 371285020313920247, 371285020353245181, 371285020919019624, 371285021124554561, 371285021826868055, 371285022529662310]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 35470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 35400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479704678652629, 362479722377374517⟩, ⟨187631509874375655, 188056020274243455⟩, true⟩

def words08 : List Nat := [371285023228237460, 371285023229390043, 371285022988001223, 371285022940828875, 371285023008535333, 371285023009695791, 371285022419166435, 371285021833440982, 371285021247265258, 371285021222690782]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 35480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 35400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362442037076827047, 362442054785907216⟩, ⟨1524823768611766060, 1525248646679272050⟩, true⟩

def words09 : List Nat := [371285021718652551, 371285022364339791, 371285023005809454, 371285023006962319, 371285022590853147, 371285022345542066, 371285022099639732, 371285021951382188, 371285020745541108, 371285019536517900]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 35490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 35400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 35400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk354
