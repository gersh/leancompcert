import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk823A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk823B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk823A

def state06 : KState := ⟨⟨360583060380876143, 360583104662584418⟩, ⟨(-63210240879533101), (-60747196397123981)⟩, true⟩

def words05 : List Nat := [360582364959505550, 360582365526046373, 360582366004921111, 360582366336879684, 360582366545722302, 360582366754850884, 360582366985850121, 360582367070037412, 360582367080054759, 360582367090233462]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 82350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 82300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595054569507759, 360595098862383445⟩, ⟨(-1051025606621566291), (-1048561642337979289)⟩, true⟩

def words06 : List Nat := [360582367247516237, 360582367532254618, 360582367885711999, 360582368239385889, 360582368457069730, 360582368527834546, 360582368686654921, 360582368845844766, 360582368963840253, 360582369119605793]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 82360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 82300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587652050185236, 360587696354290487⟩, ⟨(-441196755420877090), (-438731866100211270)⟩, true⟩

def words07 : List Nat := [360582369201294640, 360582369283110259, 360582369512021994, 360582369814949330, 360582370079784644, 360582370344825524, 360582370535250521, 360582370578835481, 360582370644445219, 360582370710439354]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 82370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 82300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598076016096462, 360598120331342339⟩, ⟨(-1300049989054912202), (-1297584181914811968)⟩, true⟩

def words08 : List Nat := [360582370820051623, 360582370879793255, 360582370880863533, 360582370827786509, 360582370774515640, 360582370684607118, 360582370832821310, 360582370981264060, 360582371037919885, 360582371230325058]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 82380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 82300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360607993443136223, 360608037769515317⟩, ⟨(-2117154708767663662), (-2114687984305980246)⟩, true⟩

def words09 : List Nat := [360582371523851914, 360582371817718183, 360582372258482322, 360582372656832138, 360582372929896063, 360582373203034943, 360582373443063800, 360582373766747241, 360582374079161355, 360582374391834149]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 82390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 82300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 82300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk823B
