import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk034

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362155912363203316, 362155912494233921⟩, ⟨1096853473009155042, 1096853775291134012⟩, true⟩

def state01 : KState := ⟨⟨362450812674127689, 362450812805967847⟩, ⟨93308738363668711, 93309043402255999⟩, true⟩

def words00 : List Nat := [371278421690205926, 371278387444949759, 371278321729730766, 371278317281900364, 371278312836655546, 371278289840364840, 371278188709232583, 371278172650441039, 371278176161710184, 371278176161804286]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 3400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 3400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362423161937581495, 362423162070245684⟩, ⟨188681932954274237, 188682240807032489⟩, true⟩

def words01 : List Nat := [371278168139780752, 371278158712836045, 371278224571300864, 371278256911529018, 371278316511300529, 371278376076224263, 371278418784130037, 371278418784220717, 371278348452353036, 371278332316095694]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 3410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 3400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362189689335101942, 362189689468576560⟩, ⟨988311810896692441, 988312121525378469⟩, true⟩

def words02 : List Nat := [371278342501589762, 371278342501680628, 371278283270829493, 371278203687845139, 371278124151297403, 371278066110972652, 371277965621036352, 371277920097184991, 371277874599857259, 371277827113336146]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 3420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 3400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362547990059386177, 362547990193684973⟩, ⟨(-241898666582847428), (-241898353123085558)⟩, true⟩

def words03 : List Nat := [371277743132738225, 371277725700308745, 371277774514955273, 371277774515046536, 371277757510001619, 371277723343554167, 371277690188815564, 371277690188916606, 371277670904883260, 371277691340699479]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 3430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 3400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362162643295755006, 362162643430877764⟩, ⟨1084240846549279842, 1084241162847731576⟩, true⟩

def words04 : List Nat := [371277705125645244, 371277705125736484, 371277607542891267, 371277552428929505, 371277497346919551, 371277453913298570, 371277299408382467, 371277143973386410, 371276988628486506, 371276916231703194]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 3440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 3400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362167698560400605, 362167698696349446⟩, ⟨1066371388539011097, 1066371707691643427⟩, true⟩

def words05 : List Nat := [371276825164597740, 371276736149047985, 371276647185027124, 371276558699693627, 371276397918657913, 371276263505151884, 371276129169360254, 371276077426344138, 371275987712637165, 371275898611867263]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 3450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 3400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494094588638616, 362494094725409258⟩, ⟨(-63732448123312761), (-63732126122949865)⟩, true⟩

def words06 : List Nat := [371275809562546709, 371275802876437240, 371275788723440713, 371275822785698586, 371275826043763796, 371275826043855746, 371275719402307143, 371275694937470564, 371275728118362281, 371275733409902791]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 3460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 3400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362395241441686816, 362395241579299471⟩, ⟨280511086003426995, 280511410929781095⟩, true⟩

def words07 : List Nat := [371275735996740313, 371275738582121231, 371275795527611046, 371275812087636579, 371275851494173477, 371275890878077806, 371275923304498384, 371275923304590697, 371275871475974301, 371275848306578144]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 3470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 3400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362100755868003195, 362100756006439766⟩, ⟨1307292332020666279, 1307292659818572295⟩, true⟩

def words08 : List Nat := [371275870398938144, 371275870399030435, 371275806653928421, 371275740327972735, 371275674040046574, 371275604355780484, 371275506754539333, 371275450508169783, 371275394294010489, 371275338430456549]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 3480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 3400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362444409483960126, 362444409623235597⟩, ⟨105999736864141619, 106000067594081115⟩, true⟩

def words09 : List Nat := [371275231131057211, 371275204986939116, 371275186681525963, 371275186681618648, 371275086304202462, 371274971376782732, 371274856515054376, 371274793381936551, 371274704012268738, 371274695356833906]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 3490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 3400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 3400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk034
