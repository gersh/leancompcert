import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk855

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476684984161166, 362476795164972179⟩, ⟨718974963769767128, 725335783583194646⟩, true⟩

def state01 : KState := ⟨⟨362464352463512664, 362464462670768415⟩, ⟨1773460700200608767, 1779823781177411299⟩, true⟩

def words00 : List Nat := [371285278527233628, 371285278522047156, 371285278333827250, 371285278119771644, 371285277904576555, 371285277692824903, 371285277411603018, 371285277238095464, 371285277063638120, 371285276888768385]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 85500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 85500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487858329853883, 362487968564053296⟩, ⟨(-236604410287690698), (-230239025221944606)⟩, true⟩

def words01 : List Nat := [371285276647374075, 371285276531195256, 371285276430190883, 371285276433202024, 371285276383931087, 371285276313537971, 371285276304988955, 371285276308295280, 371285276336337592, 371285276371197484]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 85510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 85500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481738940273938, 362481849201262385⟩, ⟨286721965612210364, 293089641816187354⟩, true⟩

def words02 : List Nat := [371285276393550441, 371285276396523381, 371285276256446257, 371285276254486773, 371285276251313741, 371285276254339546, 371285276158280291, 371285276054601094, 371285275949689419, 371285275947922226]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 85520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 85500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475463979296586, 362475574267092624⟩, ⟨823494700971100369, 829864670157841031⟩, true⟩

def words03 : List Nat := [371285276006389713, 371285276106102619, 371285276178757669, 371285276181730518, 371285276072036491, 371285276005809114, 371285275966058819, 371285275969038199, 371285275857950853, 371285275747922153]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 85530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 85500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481213995594105, 362481324309953702⟩, ⟨331652416119318189, 338024657688298209⟩, true⟩

def words04 : List Nat := [371285275650880560, 371285275654158120, 371285275690498265, 371285275773759961, 371285275834176888, 371285275837150275, 371285275715196246, 371285275599969467, 371285275500996866, 371285275504082145]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 85540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 85500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486625946457092, 362486736287944165⟩, ⟨(-131365610114822191), (-124991047658652337)⟩, true⟩

def words05 : List Nat := [371285275460119314, 371285275417117983, 371285275417583473, 371285275420950070, 371285275445481390, 371285275475878085, 371285275502192506, 371285275505186348, 371285275425789803, 371285275446583515]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472908836623936, 362473019204632627⟩, ⟨1042329075358601477, 1048705907140952117⟩, true⟩

def words06 : List Nat := [371285275489410606, 371285275492384455, 371285275366342496, 371285275240102543, 371285275112753106, 371285275022234504, 371285274879189544, 371285274841160117, 371285274802042255, 371285274737028806]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487943134980253, 362488053529832210⟩, ⟨(-244208550528561515), (-237829421630948875)⟩, true⟩

def words07 : List Nat := [371285274595825000, 371285274592609362, 371285274705362783, 371285274708337052, 371285274646196102, 371285274547116884, 371285274480879621, 371285274484166479, 371285274496095788, 371285274531904739]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473503003345685, 362473613425060513⟩, ⟨991640432203789988, 998021860164640678⟩, true⟩

def words08 : List Nat := [371285274552008345, 371285274555034883, 371285274461683636, 371285274454256566, 371285274476115311, 371285274479090011, 371285274330164942, 371285274175332552, 371285274019354891, 371285273921148428]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362460047087738980, 362460157536272547⟩, ⟨2143419366832187577, 2149803090345338441⟩, true⟩

def words09 : List Nat := [371285273786945965, 371285273708736385, 371285273629481672, 371285273546901660, 371285273281532872, 371285273022910387, 371285272762721698, 371285272639855228, 371285272348363107, 371285272058356021]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk855
