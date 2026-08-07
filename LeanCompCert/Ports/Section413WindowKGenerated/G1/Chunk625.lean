import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk625

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362468314342195446, 362468371801313597⟩, ⟨1063306723273975471, 1065732401324332859⟩, true⟩

def state01 : KState := ⟨⟨362483449427766973, 362483506905892377⟩, ⟨117317556882111500, 119744422984426634⟩, true⟩

def words00 : List Nat := [371285423248350675, 371285423234016222, 371285423128209735, 371285423128752297, 371285423128621290, 371285423092028176, 371285422713602715, 371285422592334969, 371285422507923389, 371285422510163445]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 62500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 62500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477868223397188, 362477925720857763⟩, ⟨466246229013236472, 468674303856749858⟩, true⟩

def words01 : List Nat := [371285422481105653, 371285422434881208, 371285422469658547, 371285422472022226, 371285422503931302, 371285422560105053, 371285422563654625, 371285422565776882, 371285422228132672, 371285422110874666]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 62510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 62500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475210677053797, 362475268193432226⟩, ⟨632421282335501544, 634850540018488404⟩, true⟩

def words02 : List Nat := [371285422095905058, 371285422098028229, 371285421906637692, 371285421716897762, 371285421526314923, 371285421363467225, 371285421095306067, 371285421041096068, 371285420986144389, 371285420928759565]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 62520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 62500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492971422532885, 362493028958085540⟩, ⟨(-478280389111507966), (-475849932367102762)⟩, true⟩

def words03 : List Nat := [371285420767861357, 371285420713527895, 371285420857038294, 371285420859160933, 371285420718927637, 371285420497440468, 371285420275080173, 371285420237380694, 371285420226388812, 371285420350414299]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 62530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 62500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476799630178576, 362476857184895149⟩, ⟨533103966483761964, 535535621838497840⟩, true⟩

def words04 : List Nat := [371285420474630218, 371285420476753253, 371285420260078785, 371285420151878979, 371285420042630571, 371285419947735022, 371285419623570851, 371285419299194116, 371285418973978383, 371285418905468107]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 62540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 62500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk625
