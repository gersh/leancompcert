import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk716A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk716B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk716A

def state06 : KState := ⟨⟨360600229472158767, 360600262630458503⟩, ⟨(-1286211425237228118), (-1284606470355129828)⟩, true⟩

def words05 : List Nat := [360582334623336645, 360582334759821177, 360582335040859661, 360582335293681819, 360582335362424040, 360582335431245870, 360582335651389083, 360582335969386286, 360582336220386248, 360582336471594475]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 71650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 71600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587852473231819, 360587885641210860⟩, ⟨(-399295503054269573), (-397689854504430571)⟩, true⟩

def words06 : List Nat := [360582336625511707, 360582336626528526, 360582336739206274, 360582336893424931, 360582336921012217, 360582336953857942, 360582336954772583, 360582336889967631, 360582336824970218, 360582336815960698]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 71660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 71600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560588966140529, 360560622143709823⟩, ⟨1554882896639766889, 1556489232571579975⟩, true⟩

def words07 : List Nat := [360582337088522027, 360582337361273958, 360582337482603348, 360582337483620369, 360582337410680190, 360582337243324616, 360582337075657342, 360582337065024587, 360582336860095318, 360582336558226726]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 71670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 71600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566531185453476, 360566564372620863⟩, ⟨1128978807097719415, 1130585831067659475⟩, true⟩

def words08 : List Nat := [360582336256118219, 360582336080165122, 360582336116894269, 360582336206533501, 360582336207481627, 360582336119505206, 360582335889112571, 360582335522106708, 360582335154813938, 360582334854292891]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 71680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 71600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579993869353517, 360580027066207243⟩, ⟨163738899171806426, 165346617603475704⟩, true⟩

def words09 : List Nat := [360582334635222054, 360582334293189122, 360582333950971044, 360582333807939445, 360582333808794994, 360582333708988190, 360582333609073400, 360582333412223306, 360582333186715360, 360582333155713568]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 71690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 71600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 71600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk716B
