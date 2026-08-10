import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk625A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk625B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk625A

def state06 : KState := ⟨⟨362458412395264858, 362458469969151927⟩, ⟨1683401544200584961, 1685834398764869699⟩, true⟩

def words05 : List Nat := [371285418853831053, 371285418939990001, 371285419007125990, 371285419009249353, 371285418735672062, 371285418540501297, 371285418344257857, 371285418255092205, 371285417878277573, 371285417449950599]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 62550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 62500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474093676380683, 362474151269273053⟩, ⟨702370391750845405, 704804435383636595⟩, true⟩

def words06 : List Nat := [371285417020651964, 371285416820405263, 371285416492094548, 371285416420207960, 371285416347682527, 371285416215744520, 371285415906691007, 371285415723702253, 371285415539565337, 371285415524273591]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 62560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 62500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362464492685229030, 362464550297462952⟩, ⟨1303184391470731759, 1305619645403768691⟩, true⟩

def words07 : List Nat := [371285415345837855, 371285415167190425, 371285414987729543, 371285414912789955, 371285414709857905, 371285414584997890, 371285414459416233, 371285414299852931, 371285413837619018, 371285413506881357]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 62570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 62500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467781904235976, 362467839535381555⟩, ⟨1097376691314479178, 1099813128837802068⟩, true⟩

def words08 : List Nat := [371285413174943063, 371285413099131906, 371285412842480996, 371285412565758612, 371285412288212503, 371285412088840302, 371285411795832946, 371285411608973158, 371285411421422453, 371285411242185163]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 62580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 62500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362507069065493091, 362507126715852654⟩, ⟨(-1361783569936907359), (-1359345929714204547)⟩, true⟩

def words09 : List Nat := [371285410962887936, 371285410940068676, 371285411109145948, 371285411142035825, 371285411153853339, 371285411166289593, 371285411433163077, 371285411573904851, 371285411922233867, 371285412271519270]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 62590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 62500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 62500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk625B
