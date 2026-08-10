import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk949A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk949B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk949A

def state06 : KState := ⟨⟨362489754161781649, 362489891178854848⟩, ⟨(-454082322985258909), (-445297670570078953)⟩, true⟩

def words05 : List Nat := [371285200873532362, 371285201091473333, 371285201309748531, 371285201390864673, 371285201477016808, 371285201564738987, 371285201751222397, 371285201804825248, 371285201856720261, 371285201909885797]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 94950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 94900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492564626803097, 362492701673703066⟩, ⟨(-720925499198696433), (-712138014282307277)⟩, true⟩

def words06 : List Nat := [371285202072525096, 371285202210111496, 371285202383118335, 371285202557431140, 371285202720055720, 371285202747349203, 371285202853226602, 371285202960892765, 371285203112667994, 371285203195069775]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 94960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 94900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493661413577509, 362493798490767880⟩, ⟨(-825067234687357578), (-816276872938075008)⟩, true⟩

def words07 : List Nat := [371285203276123716, 371285203358270797, 371285203538689596, 371285203680900482, 371285203838636712, 371285203997753364, 371285204147920624, 371285204196491204, 371285204289240427, 371285204383810299]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 94970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 94900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484044296769029, 362484181403623608⟩, ⟨88405124445996811, 97198303856023777⟩, true⟩

def words08 : List Nat := [371285204557878657, 371285204585237566, 371285204590539402, 371285204596955280, 371285204603531660, 371285204607237855, 371285204586617004, 371285204617974558, 371285204647862315, 371285204651374488]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 94980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 94900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493650236233399, 362493787373195418⟩, ⟨(-824111183115360481), (-815315143650100235)⟩, true⟩

def words09 : List Nat := [371285204705248966, 371285204771655862, 371285204947210438, 371285204976097954, 371285204985761542, 371285204996442387, 371285205029043405, 371285205032712892, 371285205104741520, 371285205198864095]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 94990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 94900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 94900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk949B
