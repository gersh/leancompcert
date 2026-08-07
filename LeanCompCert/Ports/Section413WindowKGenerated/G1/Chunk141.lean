import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk141

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362451262716873361, 362451265297516582⟩, ⟨468089685905569414, 468114303017251054⟩, true⟩

def state01 : KState := ⟨⟨362450357562491119, 362450360146908673⟩, ⟨480940061328686957, 480964731678233139⟩, true⟩

def words00 : List Nat := [371284464092075567, 371284464092502502, 371284461201303841, 371284458297280167, 371284455393509445, 371284452700163348, 371284447505080264, 371284447319525871, 371284447133859038, 371284446945751922]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 14100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 14100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493256129728227, 362493258717994609⟩, ⟨(-124502533820497991), (-124477809145046447)⟩, true⟩

def words01 : List Nat := [371284446279666488, 371284448029190062, 371284452319065542, 371284452319490150, 371284449932704717, 371284446674820329, 371284443822697929, 371284443823167650, 371284443008651289, 371284443633429420]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 14110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 14100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362469787374215161, 362469789966318194⟩, ⟨206789267240487171, 206814046109063719⟩, true⟩

def words02 : List Nat := [371284444235384284, 371284444235809785, 371284439553439046, 371284438570045433, 371284438167732507, 371284438168164829, 371284434623498657, 371284430448570537, 371284426487139440, 371284426487628107]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 14120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 14100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362389333363543970, 362389335959475408⟩, ⟨1344255280182716987, 1344280113166259161⟩, true⟩

def words03 : List Nat := [371284427722497919, 371284429992987294, 371284431343744489, 371284431344170020, 371284427086589131, 371284422934992939, 371284418783760225, 371284418716876124, 371284411997834436, 371284405274409373]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 14130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 14100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362447529924223982, 362447532523966166⟩, ⟨521305052778330175, 521329939665104441⟩, true⟩

def words04 : List Nat := [371284398551743003, 371284396139762311, 371284391319312055, 371284391399377167, 371284391399707299, 371284390040364592, 371284384261313280, 371284379724627327, 371284375628801717, 371284375629242852]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 14140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 14100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362465919350257408, 362465921953883094⟩, ⟨261131076533496783, 261156018391513225⟩, true⟩

def words05 : List Nat := [371284373025992631, 371284370231957087, 371284369619186136, 371284369962502796, 371284371176454759, 371284372390393211, 371284372751342284, 371284372751768444, 371284366477567888, 371284365175520913]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 14150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 14100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362414682386445149, 362414684993873498⟩, ⟨986776788094752373, 986801783818191929⟩, true⟩

def words06 : List Nat := [371284363873420981, 371284363468034807, 371284357405405943, 371284351336808759, 371284345268909853, 371284340758670699, 371284333776910949, 371284330920032834, 371284328063399470, 371284325204446413]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 14160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 14100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362526469931612522, 362526472542889511⟩, ⟨(-597727188786383248), (-597702138507942968)⟩, true⟩

def words07 : List Nat := [371284320290460109, 371284319142543131, 371284321805485198, 371284321805912703, 371284320549185128, 371284318061116471, 371284318042742618, 371284318501745347, 371284321474818798, 371284324447655893]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 14170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 14100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470529687122317, 362470532302255008⟩, ⟨195683852695669281, 195708957667732499⟩, true⟩

def words08 : List Nat := [371284326872574977, 371284326873009196, 371284326839412493, 371284328469487872, 371284331657635864, 371284331658063118, 371284329318833447, 371284326978786275, 371284324638904924, 371284324335917287]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 14180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 14100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362436004608651859, 362436007227637145⟩, ⟨685976510420601949, 686001670080461435⟩, true⟩

def words09 : List Nat := [371284325885680663, 371284328407152626, 371284330808005908, 371284330808433573, 371284327703116814, 371284324823994843, 371284324008944419, 371284324009372395, 371284320606269829, 371284317204403375]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 14190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 14100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 14100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk141
