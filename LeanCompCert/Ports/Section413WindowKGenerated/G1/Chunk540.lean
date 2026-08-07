import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk540

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470492885983641, 362470535283024670⟩, ⟨778084451940511956, 779631088847259350⟩, true⟩

def state01 : KState := ⟨⟨362472125853528300, 362472168266703153⟩, ⟨689950001779904839, 691497509997837209⟩, true⟩

def words00 : List Nat := [371284972704765236, 371284972706588461, 371284972532211742, 371284972341101244, 371284972149340411, 371284971972488995, 371284971623554489, 371284971566758768, 371284971509353579, 371284971405195985]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 54000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 54000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497621737944453, 362497664167509104⟩, ⟨(-687153072409240084), (-685604678895495180)⟩, true⟩

def words01 : List Nat := [371284971274686503, 371284971382176064, 371284971831037791, 371284971868515863, 371284971878007887, 371284971888082623, 371284972152518758, 371284972246967859, 371284972483168685, 371284972720129465]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 54010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 54000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487069624309127, 362487112070231097⟩, ⟨(-117150579949927736), (-115601302728632134)⟩, true⟩

def words02 : List Nat := [371284972894822443, 371284972896636315, 371284972628992939, 371284972645411122, 371284972763686033, 371284972765536572, 371284972667462138, 371284972516927975, 371284972491950314, 371284972533618252]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 54020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 54000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477084228768421, 362477126691066882⟩, ⟨422472528708834760, 424022690833641670⟩, true⟩

def words03 : List Nat := [371284972872778282, 371284973212699829, 371284973514828204, 371284973516642591, 371284973362457675, 371284973274162881, 371284973436426653, 371284973438241928, 371284973294037044, 371284973150926868]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 54030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 54000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478110593713275, 362478153072243313⟩, ⟨367005548487082280, 368556587849904754⟩, true⟩

def words04 : List Nat := [371284973089876352, 371284973091875738, 371284973004848995, 371284973004995507, 371284973004607103, 371284972951335326, 371284972490554105, 371284972173685108, 371284971878645293, 371284971880529158]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 54040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 54000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489246610032429, 362489289105085866⟩, ⟨(-234928084743357717), (-233376152210619845)⟩, true⟩

def words05 : List Nat := [371284971755731735, 371284971615299453, 371284971652187019, 371284971770125088, 371284971955747481, 371284972142072113, 371284972297889883, 371284972299704934, 371284972118904776, 371284972200992146]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362462748201638972, 362462790712871368⟩, ⟨1197713893532186718, 1199266700784889912⟩, true⟩

def words06 : List Nat := [371284972424504819, 371284972426320053, 371284972194197022, 371284971961948662, 371284971728998012, 371284971509814646, 371284971118918465, 371284970956770804, 371284970793999895, 371284970603768074]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485295102121715, 362485337629790290⟩, ⟨(-21487372382808566), (-19933676344570962)⟩, true⟩

def words07 : List Nat := [371284970194800744, 371284970099638248, 371284970150510897, 371284970152330420, 371284969946425975, 371284969651741693, 371284969356337209, 371284969276398352, 371284969031628428, 371284969040519667]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362465417451236105, 362465459995298781⟩, ⟨1053611075200697908, 1055165657917879026⟩, true⟩

def words08 : List Nat := [371284969046724782, 371284969048572167, 371284968832210809, 371284968896279030, 371284969019858074, 371284969021674071, 371284968690011740, 371284968275243204, 371284967859757586, 371284967587421501]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472808668666897, 362472851229079772⟩, ⟨653860540545953758, 655416007726125550⟩, true⟩

def words09 : List Nat := [371284967228009873, 371284967210654776, 371284967192714113, 371284967182179336, 371284966898104362, 371284966693514805, 371284966569596307, 371284966571424983, 371284966349473337, 371284966127558998]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk540
