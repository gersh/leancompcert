import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk190

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362371222164829750, 362371226976475813⟩, ⟨2183427832388916633, 2183489666576237877⟩, true⟩

def state01 : KState := ⟨⟨362458874365310145, 362458879182215794⟩, ⟨517716984164182458, 517778918309873818⟩, true⟩

def words00 : List Nat := [371286141437512396, 371286138147867183, 371286133472452343, 371286131077684975, 371286128683000481, 371286125669863935, 371286120886111756, 371286118462113762, 371286116368262721, 371286116368870706]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 19000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 19000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362439502412846353, 362439507235100440⟩, ⟨886340664763377627, 886402700610756119⟩, true⟩

def words01 : List Nat := [371286114936603638, 371286113517354595, 371286113431918252, 371286113432565379, 371286114179899321, 371286114978728579, 371286115761468235, 371286115762056435, 371286113401929176, 371286110952272405]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 19010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 19000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362421158582990173, 362421163410483354⟩, ⟨1235279668470652528, 1235341803992434510⟩, true⟩

def words02 : List Nat := [371286108502553284, 371286108004647218, 371286103833069616, 371286099260480177, 371286094688139365, 371286090940194085, 371286086204272412, 371286083766129752, 371286081328050747, 371286078902022631]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 19020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 19000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362507581076099106, 362507585908923271⟩, ⟨(-409807147603249886), (-409744910606893966)⟩, true⟩

def words03 : List Nat := [371286075491382926, 371286074828968794, 371286074663348853, 371286074663937808, 371286072109422631, 371286069100999715, 371286066092659863, 371286065830932549, 371286065692348175, 371286066823234133]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 19030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 19000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362441542493205101, 362441547331334393⟩, ⟨847705945824155592, 847768283857560452⟩, true⟩

def words04 : List Nat := [371286067359677054, 371286067360265863, 371286064230782015, 371286063502835555, 371286062774677100, 371286062596992527, 371286059206915138, 371286055243113903, 371286051279485530, 371286049603452901]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 19040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 19000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362421523599944118, 362421528443372096⟩, ⟨1229441928285349971, 1229504367286085951⟩, true⟩

def words05 : List Nat := [371286047674109773, 371286048080915994, 371286048357387976, 371286048357987185, 371286046348319493, 371286044708244589, 371286043068032650, 371286042272952897, 371286038877014564, 371286035493072311]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 19050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 19000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362421351501907155, 362421356350612905⟩, ⟨1232736336200128697, 1232798875822386159⟩, true⟩

def words06 : List Nat := [371286032109237008, 371286029815705357, 371286026167101516, 371286023941530084, 371286021716004796, 371286019047096953, 371286012721696065, 371286008346079939, 371286003970613538, 371286002332564787]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 19060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 19000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362441301171085183, 362441306025171853⟩, ⟨852276206577241613, 852338848840102857⟩, true⟩

def words07 : List Nat := [371285998943258879, 371285995438775392, 371285991934412425, 371285991166721376, 371285989587685952, 371285988150213197, 371285986712696866, 371285985289024177, 371285980213268902, 371285977872595339]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 19070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 19000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362452787248176829, 362452792107524222⟩, ⟨633279775517960320, 633342518182889220⟩, true⟩

def words08 : List Nat := [371285975924827332, 371285975925428056, 371285974744784404, 371285973578690921, 371285972412499818, 371285971275868299, 371285968982493741, 371285969202602840, 371285969203056365, 371285968771651142]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 19080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 19000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362505095236997589, 362505100101675717⟩, ⟨(-365555153864193220), (-365492309408737398)⟩, true⟩

def words09 : List Nat := [371285967051779884, 371285967070021089, 371285969378765393, 371285969379355888, 371285968041781485, 371285966336028068, 371285964680521677, 371285964681177790, 371285964378012278, 371285965380487888]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 19090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 19000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 19000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk190
