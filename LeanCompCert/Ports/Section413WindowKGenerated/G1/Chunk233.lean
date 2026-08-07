import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk233

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362568338373005745, 362568345737249565⟩, ⟨(-1956772381270075559), (-1956656358958774807)⟩, true⟩

def state01 : KState := ⟨⟨362490692444634075, 362490699815490783⟩, ⟨(-147285762197098379), (-147169585771820077)⟩, true⟩

def words00 : List Nat := [371284376277996715, 371284377744980204, 371284379955036156, 371284382165277189, 371284384689419095, 371284385119214093, 371284385339227608, 371284385559460085, 371284386233091128, 371284386504788891]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 23300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 23300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362454753279172363, 362454760656618319⟩, ⟨690863973008930741, 690980303063043199⟩, true⟩

def words01 : List Nat := [371284388617273843, 371284390729884093, 371284392772854333, 371284392773586329, 371284392514725260, 371284392664433991, 371284393556959568, 371284393557691845, 371284392299640010, 371284391029819994]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 23310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 23300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362511841618959308, 362511849002962412⟩, ⟨(-640541027718018357), (-640424544718976601)⟩, true⟩

def words02 : List Nat := [371284390328926509, 371284390329737755, 371284391881816576, 371284393475805801, 371284394784156059, 371284394784888431, 371284394962288599, 371284395970957991, 371284398314475546, 371284399491809055]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 23320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 23300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362531283436011979, 362531290826682678⟩, ⟨(-1094283634046574459), (-1094166995457653011)⟩, true⟩

def words03 : List Nat := [371284399951988512, 371284400412356552, 371284402710194639, 371284404091939873, 371284405787411233, 371284407483020575, 371284409167469632, 371284409339556937, 371284411348687434, 371284413358045617]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 23330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 23300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362496441196894827, 362496448594094380⟩, ⟨(-280806701464688433), (-280689910458114915)⟩, true⟩

def words04 : List Nat := [371284416498715644, 371284418006596949, 371284419517124733, 371284421027778413, 371284422238316606, 371284422542063883, 371284424247581727, 371284425953247148, 371284427612158910, 371284428127713578]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 23340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 23300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362522582627846003, 362522590031687836⟩, ⟨(-891312435868192135), (-891195489731460319)⟩, true⟩

def words05 : List Nat := [371284429974299832, 371284431821126306, 371284434583299562, 371284434903544243, 371284434923202484, 371284434943073995, 371284436796948718, 371284437905267603, 371284439538999291, 371284441172917601]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 23350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 23300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362513055936405312, 362513063346864143⟩, ⟨(-668926876748931395), (-668809776005976377)⟩, true⟩

def words06 : List Nat := [371284442754082793, 371284442754816337, 371284442549455788, 371284443204462255, 371284444414557115, 371284444415303389, 371284444116632624, 371284443814502149, 371284445041532685, 371284446266892984]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 23360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 23300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491955338747814, 362491962755819606⟩, ⟨(-175470883753275459), (-175353628431775027)⟩, true⟩

def words07 : List Nat := [371284449324033888, 371284452381203764, 371284455096983210, 371284456614947782, 371284457903006645, 371284459191320570, 371284461953387887, 371284462278437939, 371284462599794781, 371284462921405690]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 23370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 23300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362509715211501108, 362509722635138812⟩, ⟨(-590609712048675508), (-590492303181821382)⟩, true⟩

def words08 : List Nat := [371284464741249518, 371284465658275462, 371284468062902500, 371284470467628052, 371284472580841677, 371284473068253742, 371284473979729519, 371284474891487035, 371284477131891202, 371284478211934083]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 23380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 23300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362518258874398357, 362518266304746609⟩, ⟨(-790425775340307929), (-790308209481321451)⟩, true⟩

def words09 : List Nat := [371284479201173351, 371284480190581611, 371284482705703854, 371284484547606823, 371284486942976198, 371284489338414395, 371284491387866649, 371284491388601592, 371284492448711759, 371284493892906033]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 23390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 23300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 23300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk233
