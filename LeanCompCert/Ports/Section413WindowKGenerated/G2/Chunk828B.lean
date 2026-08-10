import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk828A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk828B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk828A

def state06 : KState := ⟨⟨360581879270165873, 360581924112304176⟩, ⟨36946633010376805, 39455974737958951⟩, true⟩

def words05 : List Nat := [360582399222967122, 360582399320856075, 360582399498382192, 360582399749635174, 360582399939831919, 360582400130217798, 360582400235754023, 360582400292094649, 360582400293074302, 360582400288682863]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 82850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 82800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360582050614324051, 360582095467649139⟩, ⟨22708349902362992, 25218618622989648⟩, true⟩

def words06 : List Nat := [360582400289893006, 360582400291086823, 360582400255965746, 360582400111053768, 360582399965951476, 360582399784592852, 360582399768413696, 360582399821515971, 360582399822576139, 360582399783066335]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 82860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 82800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604003403050803, 360604048267612125⟩, ⟨(-1796672825852890050), (-1794161625930448010)⟩, true⟩

def words07 : List Nat := [360582399886446686, 360582399993857797, 360582400097041908, 360582400178082055, 360582400179187563, 360582400127078894, 360582400142768572, 360582400301187025, 360582400563344289, 360582400825786732]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 82870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 82800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596351065365908, 360596395941247299⟩, ⟨(-1162498244966478340), (-1159986106779645584)⟩, true⟩

def words08 : List Nat := [360582401015074204, 360582401128418320, 360582401387040075, 360582401646004667, 360582401802011590, 360582401813018027, 360582401814095269, 360582401713709407, 360582401657011359, 360582401827208626]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 82880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 82800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589064388458275, 360589109275529173⟩, ⟨(-558383080307002379), (-555870014566866081)⟩, true⟩

def words09 : List Nat := [360582402142483176, 360582402457983158, 360582402700265952, 360582402983912760, 360582403205230432, 360582403426866741, 360582403712421387, 360582403884567696, 360582403966522081, 360582404048637256]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 82890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 82800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 82800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk828B
