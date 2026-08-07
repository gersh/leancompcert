import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk492

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492552313638261, 362492587245436657⟩, ⟨(-375634743908935401), (-374473614559919575)⟩, true⟩

def state01 : KState := ⟨⟨362488208694008791, 362488243640422552⟩, ⟨(-161907126174536864), (-160745277673791146)⟩, true⟩

def words00 : List Nat := [371284976715564256, 371284976793574866, 371284976794842660, 371284976726208492, 371284976660259508, 371284976662066702, 371284976698459022, 371284976923830733, 371284977122176291, 371284977190285921]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 49200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 49200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362518006105591668, 362518041066816253⟩, ⟨(-1628355908134616987), (-1627193330717486961)⟩, true⟩

def words01 : List Nat := [371284977669631332, 371284978149806186, 371284978939482498, 371284979360034112, 371284979691061127, 371284980022604524, 371284980485667491, 371284980795872091, 371284981468669508, 371284982142155692]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 49210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 49200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495634386579703, 362495669362612153⟩, ⟨(-527154914700382021), (-525991608364117917)⟩, true⟩

def words02 : List Nat := [371284982815248459, 371284982939235757, 371284983474326867, 371284984010293748, 371284984562629451, 371284984615253603, 371284984639270423, 371284984663825870, 371284984989235180, 371284985208149231]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 49220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 49200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479436331557117, 362479471322396837⟩, ⟨270366145705789994, 271530181079860362⟩, true⟩

def words03 : List Nat := [371284985519122471, 371284985830751222, 371284986143054056, 371284986144695417, 371284985953864577, 371284985841549766, 371284985962319764, 371284985963989709, 371284985855380520, 371284985745245738]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 49230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 49200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476324303720242, 362476359309263371⟩, ⟨423707643186735498, 424872402628316716⟩, true⟩

def words04 : List Nat := [371284985836168750, 371284985881457525, 371284986221092789, 371284986561373106, 371284986776553348, 371284986778195103, 371284986444265653, 371284986261864383, 371284986158376723, 371284986160078160]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 49240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 49200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362480295966455362, 362480330986943425⟩, ⟨228144484627290613, 229309980184861271⟩, true⟩

def words05 : List Nat := [371284985986144876, 371284985814129118, 371284985878736927, 371284985911389002, 371284986071591392, 371284986232430248, 371284986387170434, 371284986388823484, 371284986174441288, 371284986081953268]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 49250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 49200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472973631224190, 362473008666347786⟩, ⟨588915167014165431, 590081383593533513⟩, true⟩

def words06 : List Nat := [371284986305074242, 371284986306716439, 371284986075859530, 371284985846954629, 371284985617410014, 371284985447746439, 371284985187446213, 371284985209197714, 371284985210434081, 371284985150691069]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 49260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 49200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501644476743290, 362501679526746735⟩, ⟨(-823882282426768634), (-822715332645361766)⟩, true⟩

def words07 : List Nat := [371284984976053782, 371284985045350828, 371284985287189717, 371284985288832571, 371284985036770797, 371284984736589216, 371284984544549441, 371284984546360065, 371284984814348775, 371284985155028520]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 49270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 49200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476779065663937, 362476814130470214⟩, ⟨401546143941325413, 402713823282316425⟩, true⟩

def words08 : List Nat := [371284985496429844, 371284985498073469, 371284985372686466, 371284985383819260, 371284985522217655, 371284985523864237, 371284985238049070, 371284984868971394, 371284984499227966, 371284984425119886]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 49280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 49200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471319583154887, 362471354662743921⟩, ⟨670732553310630528, 671900961368607180⟩, true⟩

def words09 : List Nat := [371284984306685787, 371284984354651360, 371284984399825190, 371284984401497679, 371284984111308619, 371284983950052348, 371284984035061226, 371284984036704788, 371284983760103176, 371284983485489735]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 49290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 49200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 49200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk492
