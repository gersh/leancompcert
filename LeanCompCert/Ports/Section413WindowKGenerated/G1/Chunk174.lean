import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk174

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487125523785943, 362487129527772553⟩, ⟨(-25596938391842179), (-25549813954031243)⟩, true⟩

def state01 : KState := ⟨⟨362483347460265388, 362483351469015826⟩, ⟨40488743298164864, 40535950651288230⟩, true⟩

def words00 : List Nat := [371285664616586533, 371285666300925230, 371285667975093128, 371285669649244642, 371285671946855062, 371285672611538892, 371285675220698213, 371285677829781129, 371285679782687968, 371285679783240484]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 17400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 17400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362554028732504137, 362554032746072474⟩, ⟨(-1190540013329231882), (-1190492722071592700)⟩, true⟩

def words01 : List Nat := [371285681837880466, 371285684026264356, 371285687899853273, 371285687900387469, 371285687386192210, 371285686366957262, 371285687621148951, 371285688252197991, 371285692175895907, 371285696099377589]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 17410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 17400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362449321229940756, 362449325248338994⟩, ⟨633809572056631881, 633856947475172073⟩, true⟩

def words02 : List Nat := [371285700012351008, 371285700315305234, 371285701431541784, 371285702547935446, 371285703526515138, 371285703527049699, 371285700123665036, 371285696330126623, 371285692536812285, 371285691108779337]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 17420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 17400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362384804421726004, 362384808444938989⟩, ⟨1759020505830908376, 1759067965195541576⟩, true⟩

def words03 : List Nat := [371285690225689163, 371285691428957137, 371285692464389399, 371285692464925139, 371285690010553373, 371285687699390172, 371285685388228981, 371285683990811326, 371285678216978376, 371285672433769009]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 17430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 17400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362501836717834935, 362501840745840694⟩, ⟨(-282471649534516905), (-282424106559908981)⟩, true⟩

def words04 : List Nat := [371285666650978712, 371285663614462308, 371285659545566603, 371285658762009282, 371285657978370530, 371285656696711323, 371285653585770602, 371285653290890975, 371285655982732501, 371285656910727526]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 17440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 17400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362498785156754472, 362498789189642731⟩, ⟨(-229144352048776383), (-229096723849779115)⟩, true⟩

def words05 : List Nat := [371285657196350489, 371285657482105408, 371285660405526447, 371285661692100961, 371285663953270689, 371285666214392231, 371285667697598610, 371285667698144124, 371285667956228887, 371285668708350149]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 17450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 17400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362463690860875168, 362463694898528655⟩, ⟨383803398614486952, 383851110039473674⟩, true⟩

def words06 : List Nat := [371285671824254118, 371285671824789946, 371285670576448082, 371285669319412133, 371285668062317547, 371285666982114172, 371285665302033656, 371285666099877871, 371285666913431296, 371285666913985981]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 17460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 17400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362514146236736569, 362514150279252336⟩, ⟨(-497702967441054480), (-497655171048698394)⟩, true⟩

def words07 : List Nat := [371285667673194369, 371285669690097352, 371285674387689812, 371285674726734417, 371285674727149908, 371285674481765617, 371285677261753894, 371285678673999952, 371285680303183470, 371285681932415846]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 17470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 17400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362500208012854866, 362500212060206867⟩, ⟨(-254237205783554574), (-254189324828876434)⟩, true⟩

def words08 : List Nat := [371285683553692998, 371285683554229373, 371285681356737394, 371285681893220837, 371285683013378198, 371285683013923957, 371285681432508275, 371285679415882617, 371285678650510423, 371285679482033585]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 17480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 17400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482550913786698, 362482554965972694⟩, ⟨54848641423039890, 54896606948904818⟩, true⟩

def words09 : List Nat := [371285683580977484, 371285687679665271, 371285690821259930, 371285690821796875, 371285689613576035, 371285689373509389, 371285692157857907, 371285692158397449, 371285692093597279, 371285691914941203]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 17490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 17400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 17400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk174
