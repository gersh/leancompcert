import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk551A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk551B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk551A

def state06 : KState := ⟨⟨362507986892111664, 362508031205667553⟩, ⟨(-1276627843673240802), (-1274976598862334718)⟩, true⟩

def words05 : List Nat := [371284915202352528, 371284915424113512, 371284915781198035, 371284915921965974, 371284916009651315, 371284916097893687, 371284916429220032, 371284916631681398, 371284917051992217, 371284917473159761]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478279502182434, 362478323832473751⟩, ⟨362136488723921012, 363788656747673100⟩, true⟩

def words06 : List Nat := [371284917875704320, 371284917877559800, 371284918133976514, 371284918427864505, 371284918649633689, 371284918651489350, 371284918435738760, 371284918130721210, 371284917824934558, 371284917790362961]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478179240862709, 362478223587844265⟩, ⟨367759440446074610, 369412529354108348⟩, true⟩

def words07 : List Nat := [371284917880709696, 371284918091314276, 371284918285253816, 371284918287142521, 371284918228705362, 371284918249619448, 371284918505931707, 371284918507788252, 371284918388678230, 371284918269420092]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482130182794427, 362482174546418806⟩, ⟨149770856294739857, 151424863637068519⟩, true⟩

def words08 : List Nat := [371284918164460964, 371284918166511756, 371284918225831657, 371284918404974705, 371284918561618393, 371284918563475576, 371284918339636610, 371284918213322948, 371284918245595953, 371284918247517503]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489234119082734, 362489278499634708⟩, ⟨(-242323193224674777), (-240668251564895291)⟩, true⟩

def words09 : List Nat := [371284918199192836, 371284918152098426, 371284918321754138, 371284918376937331, 371284918452885869, 371284918529499481, 371284918604755053, 371284918606633370, 371284918565208363, 371284918646523988]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk551B
