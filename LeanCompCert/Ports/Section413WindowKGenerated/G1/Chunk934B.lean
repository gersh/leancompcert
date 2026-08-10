import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk934A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk934B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk934A

def state06 : KState := ⟨⟨362470359260315445, 362470491819394973⟩, ⟨1361294838382266082, 1369659493270729004⟩, true⟩

def words05 : List Nat := [371285147177092868, 371285147254534325, 371285147330577435, 371285147333848186, 371285147257111148, 371285147216946290, 371285147175025584, 371285147160779762, 371285147006725104, 371285146853562219]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480009437968421, 362480142026309486⟩, ⟨459364714391857999, 467732104215133703⟩, true⟩

def words06 : List Nat := [371285146698980914, 371285146629292374, 371285146504841688, 371285146496334843, 371285146486743717, 371285146462290978, 371285146319679905, 371285146217532683, 371285146113725765, 371285146114297238]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490601868600863, 362490734486821402⟩, ⟨(-530784023078529489), (-522413840275010095)⟩, true⟩

def words07 : List Nat := [371285146063248455, 371285145991107140, 371285145948975166, 371285145952618357, 371285145938598318, 371285145951423963, 371285145962865129, 371285145966216513, 371285145973524080, 371285146037400932]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485136851046570, 362485269498371135⟩, ⟨(-19860098203393304), (-11487194600210080)⟩, true⟩

def words08 : List Nat := [371285146213874214, 371285146257948442, 371285146292870017, 371285146328824520, 371285146368405614, 371285146372011588, 371285146449151824, 371285146547438131, 371285146624146188, 371285146628847864]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496791808589890, 362496924485523420⟩, ⟨(-1109505185358078237), (-1101129513471018285)⟩, true⟩

def words09 : List Nat := [371285146746842647, 371285146866604184, 371285147099053737, 371285147180046337, 371285147233450297, 371285147287921354, 371285147455455568, 371285147567378208, 371285147695598058, 371285147825236675]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk934B
