import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk861A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk861B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk861A

def state06 : KState := ⟨⟨362473005786258054, 362473117741145919⟩, ⟨1037048841566341705, 1043561931455996705⟩, true⟩

def words05 : List Nat := [371285230895667185, 371285230705878496, 371285230514825362, 371285230439923762, 371285230304956908, 371285230212540851, 371285230119100029, 371285230025465487, 371285229785250632, 371285229648428371]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469633835276163, 362469745816873885⟩, ⟨1327595741357704422, 1334111132710325640⟩, true⟩

def words06 : List Nat := [371285229509887048, 371285229506831658, 371285229342724588, 371285229131735526, 371285228919619631, 371285228738889308, 371285228489549505, 371285228370853518, 371285228251121364, 371285228132444389]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482888907312600, 362483000915946378⟩, ⟨185346444645478423, 191864165832907473⟩, true⟩

def words07 : List Nat := [371285227954806701, 371285227913181681, 371285227880164716, 371285227883181813, 371285227774859704, 371285227644810009, 371285227513546429, 371285227415647924, 371285227257373537, 371285227234881548]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473685710860547, 362473797746553622⟩, ⟨978483588310411724, 985003641596273222⟩, true⟩

def words08 : List Nat := [371285227211291724, 371285227177763796, 371285226986723307, 371285226931842049, 371285226875357738, 371285226825233952, 371285226594963942, 371285226365816705, 371285226135479003, 371285226028739448]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470100108411152, 362470212171131731⟩, ⟨1287549372503639850, 1294071755428587992⟩, true⟩

def words09 : List Nat := [371285225898215560, 371285225825487879, 371285225751731473, 371285225666868465, 371285225419425836, 371285225214773261, 371285225008579206, 371285224937826421, 371285224775250028, 371285224604489372]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk861B
