import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk629A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk629B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk629A

def state06 : KState := ⟨⟨362488223948267287, 362488282289973850⟩, ⟨(-183284333013875031), (-180803289850768813)⟩, true⟩

def words05 : List Nat := [371285410776801972, 371285410898433670, 371285411085710902, 371285411087848819, 371285410939112544, 371285410746678520, 371285410583461658, 371285410585858523, 371285410570741399, 371285410618782942]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 62950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 62900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477268114674010, 362477326475654075⟩, ⟨506489209856553604, 508971466577654472⟩, true⟩

def words06 : List Nat := [371285410673728362, 371285410675866600, 371285410394526368, 371285410338894691, 371285410282214109, 371285410234330543, 371285409926217902, 371285409612581487, 371285409298060083, 371285409236755833]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 62960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 62900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467907595594066, 362467965975839926⟩, ⟨1096063449232491888, 1098546919215985470⟩, true⟩

def words07 : List Nat := [371285409233704564, 371285409359907874, 371285409486855177, 371285409488998057, 371285409377158424, 371285409268193790, 371285409265398144, 371285409267536830, 371285409040498215, 371285408765919571]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 62970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 62900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362503445579726020, 362503503979110718⟩, ⟨(-1142262294165743789), (-1139777618719140635)⟩, true⟩

def words08 : List Nat := [371285408490417316, 371285408467979230, 371285408418760411, 371285408521824413, 371285408605700527, 371285408607891619, 371285408748847058, 371285408947180122, 371285409396507013, 371285409685978062]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 62980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 62900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362501437702232958, 362501496121183555⟩, ⟨(-1015776897122915737), (-1013290989127113321)⟩, true⟩

def words09 : List Nat := [371285409972513654, 371285410259775703, 371285410650353361, 371285410916332624, 371285411245193037, 371285411574842228, 371285411846169111, 371285411877727575, 371285412134484771, 371285412392526437]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 62990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 62900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 62900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk629B
