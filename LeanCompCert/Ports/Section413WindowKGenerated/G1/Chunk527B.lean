import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk527A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk527B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk527A

def state06 : KState := ⟨⟨362494630660724575, 362494671057261623⟩, ⟨(-509919536498395754), (-508479691934768178)⟩, true⟩

def words05 : List Nat := [371285033256507942, 371285033201554152, 371285033401706292, 371285033403482504, 371285033317125414, 371285033171538346, 371285033236624800, 371285033272960559, 371285033456853660, 371285033641520171]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 52750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 52700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490455339002732, 362490495751492646⟩, ⟨(-289657958604015132), (-288217272285189458)⟩, true⟩

def words06 : List Nat := [371285033810072497, 371285033811845385, 371285033830074033, 371285033973861003, 371285034194089564, 371285034195888519, 371285034118286940, 371285033955424354, 371285033985741166, 371285034091257192]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 52760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 52700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483988696110405, 362484029124532740⟩, ⟨51674664758740953, 53116191911619863⟩, true⟩

def words07 : List Nat := [371285034534077487, 371285034977583365, 371285035344816998, 371285035346585534, 371285035235451720, 371285035232198138, 371285035528634367, 371285035530414907, 371285035511269235, 371285035494216553]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 52770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 52700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485906703055460, 362485947147293062⟩, ⟨(-49455714636644804), (-48013352672102836)⟩, true⟩

def words08 : List Nat := [371285035763385241, 371285035917611861, 371285036429580546, 371285036942271393, 371285037336381508, 371285037338150572, 371285037316987502, 371285037382024201, 371285037629404375, 371285037648464245]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 52780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 52700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483769359633930, 362483809820015933⟩, ⟨63414744348214688, 64857958654550962⟩, true⟩

def words09 : List Nat := [371285037667359035, 371285037686865016, 371285037886514615, 371285037958928475, 371285038140721494, 371285038323168480, 371285038505393947, 371285038507163404, 371285038211474842, 371285038190444997]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 52790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 52700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 52700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk527B
