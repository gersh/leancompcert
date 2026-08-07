import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk657

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362475769173136730, 362475832916506885⟩, ⟨632260123102470656, 635088712484143292⟩, true⟩

def state01 : KState := ⟨⟨362477924981452803, 362477988744777205⟩, ⟨490685253967011736, 493515154446263034⟩, true⟩

def words00 : List Nat := [371285499350145301, 371285499352438546, 371285499333212921, 371285499273778812, 371285499213472914, 371285499172764266, 371285499119538410, 371285499210312932, 371285499245495156, 371285499247812455]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 65700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 65700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362515009360741690, 362515073144332762⟩, ⟨(-1946320272772353394), (-1943489040470571964)⟩, true⟩

def words01 : List Nat := [371285499188528251, 371285499244727840, 371285499531172839, 371285499661597676, 371285499766267250, 371285499871643961, 371285500207494561, 371285500428571812, 371285500880071131, 371285501332575933]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 65710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 65700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494936795934689, 362495000599756317⟩, ⟨(-627119197557408545), (-624286635600276893)⟩, true⟩

def words02 : List Nat := [371285501779087428, 371285501989067693, 371285502240912195, 371285502493857657, 371285502751780085, 371285502754019823, 371285502732764005, 371285502697310540, 371285502854337052, 371285503001429801]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 65720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 65700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482423068161250, 362482486892110994⟩, ⟨195569723872497168, 198403608953514972⟩, true⟩

def words03 : List Nat := [371285503378793340, 371285503757036122, 371285504134444123, 371285504262124455, 371285504459803064, 371285504658646323, 371285504952253536, 371285504954493338, 371285504939914973, 371285504896506393]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 65730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 65700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483168989786110, 362483232833775138⟩, ⟨146573604219358343, 149408806786298499⟩, true⟩

def words04 : List Nat := [371285504954692971, 371285504957161159, 371285505103637810, 371285505264127039, 371285505387795668, 371285505390036054, 371285505236867717, 371285505168556884, 371285505208742913, 371285505211064664]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 65740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 65700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362494033704154923, 362494097568619979⟩, ⟨(-567846189438366195), (-565009640471282445)⟩, true⟩

def words05 : List Nat := [371285505178209738, 371285505104565236, 371285505145848915, 371285505180378658, 371285505284655214, 371285505389772663, 371285505473146161, 371285505475442152, 371285505570062099, 371285505703525603]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482005632581289, 362482069516964920⟩, ⟨223230826651270409, 226068685569878995⟩, true⟩

def words06 : List Nat := [371285506066816347, 371285506148472893, 371285506229186684, 371285506310619393, 371285506402408624, 371285506404877952, 371285506535569826, 371285506679128012, 371285506776095384, 371285506778414972]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495517565214731, 362495581469886588⟩, ⟨(-665508410412974550), (-662669217040846180)⟩, true⟩

def words07 : List Nat := [371285506877769276, 371285507030593211, 371285507292455850, 371285507294696861, 371285507248798102, 371285507166705373, 371285507230143447, 371285507289902934, 371285507444599453, 371285507600273161]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495348409446149, 362495412334328259⟩, ⟨(-654441090342828272), (-651600567436743432)⟩, true⟩

def words08 : List Nat := [371285507754771774, 371285507757014917, 371285507748734351, 371285507849116642, 371285507977016980, 371285507979298940, 371285507947690313, 371285507916701588, 371285508082348590, 371285508235478314]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479923093191517, 362479987038304106⟩, ⟨360507721533719314, 363349575505295954⟩, true⟩

def words09 : List Nat := [371285508506185867, 371285508777819118, 371285509011157162, 371285509013399386, 371285509001207129, 371285509032267669, 371285509230418570, 371285509232660694, 371285509149662784, 371285509068326983]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk657
