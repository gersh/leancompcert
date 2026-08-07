import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk833

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491979473249782, 362492083846691504⟩, ⟨(-569216743800624385), (-563346096587585721)⟩, true⟩

def state01 : KState := ⟨⟨362478005495570257, 362478109895052357⟩, ⟨594838259073550443, 600711075582974769⟩, true⟩

def words00 : List Nat := [371285321152712388, 371285321155601459, 371285321046467756, 371285321012757611, 371285320984355572, 371285320987248939, 371285320840702144, 371285320667709776, 371285320493571164, 371285320446913874]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 83300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 83300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473232025801199, 362473336451319617⟩, ⟨992620591720077187, 998495577449132979⟩, true⟩

def words01 : List Nat := [371285320419867955, 371285320480586109, 371285320540240866, 371285320543200747, 371285320531656542, 371285320544456654, 371285320594808637, 371285320597698395, 371285320456225112, 371285320315667303]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 83310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 83300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477415827088059, 362477520278529920⟩, ⟨644010706638208305, 649887852433986267⟩, true⟩

def words02 : List Nat := [371285320173833791, 371285320092517376, 371285319938239867, 371285319905550175, 371285319872004054, 371285319787539559, 371285319530696669, 371285319401733230, 371285319271170083, 371285319244717776]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 83320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 83300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481406357806034, 362481510835545382⟩, ⟨311475623255119882, 317354960553887896⟩, true⟩

def words03 : List Nat := [371285319153309114, 371285319061606725, 371285319004597314, 371285319007799430, 371285319007388876, 371285319012980460, 371285319017369620, 371285319020260211, 371285318832546085, 371285318790435638]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 83330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 83300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477870940485847, 362477975443996558⟩, ⟨606190332703953876, 612071817923130948⟩, true⟩

def words04 : List Nat := [371285318844988820, 371285318847929872, 371285318828990418, 371285318809260711, 371285318802182218, 371285318805370905, 371285318795244560, 371285318829230061, 371285318834136580, 371285318837133009]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 83340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 83300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492728569628019, 362492833099323605⟩, ⟨(-632293683469493292), (-626410015611458558)⟩, true⟩

def words05 : List Nat := [371285318753015538, 371285318758524961, 371285318832903995, 371285318835795498, 371285318737385230, 371285318616776618, 371285318515096450, 371285318518334498, 371285318580490626, 371285318673925500]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 83350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 83300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469171538705508, 362469276094497374⟩, ⟨1331511213101973256, 1337397056480703940⟩, true⟩

def words06 : List Nat := [371285318753441214, 371285318756332595, 371285318643877672, 371285318592081677, 371285318538888089, 371285318530534344, 371285318350145157, 371285318155807208, 371285317960285850, 371285317800824359]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 83360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 83300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362454185053404180, 362454289635199812⟩, ⟨2581069682307099277, 2586957693750747519⟩, true⟩

def words07 : List Nat := [371285317610372115, 371285317553597343, 371285317495866805, 371285317438676267, 371285317188894691, 371285316942652270, 371285316694875589, 371285316491537528, 371285316121764442, 371285315752898910]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 83370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 83300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471276143144869, 362471380750795123⟩, ⟨1155960878640389255, 1161851045976437403⟩, true⟩

def words08 : List Nat := [371285315382759784, 371285315149750983, 371285314861317932, 371285314717976851, 371285314573685048, 371285314396901566, 371285314042714003, 371285313810863309, 371285313577549470, 371285313489084804]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 83380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 83300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479748286373336, 362479852920448709⟩, ⟨449397841251446221, 455290212306663329⟩, true⟩

def words09 : List Nat := [371285313324227396, 371285313112445566, 371285312899449862, 371285312812834784, 371285312665770108, 371285312545880933, 371285312425043934, 371285312304819954, 371285312097546924, 371285312035704185]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 83390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 83300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 83300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk833
