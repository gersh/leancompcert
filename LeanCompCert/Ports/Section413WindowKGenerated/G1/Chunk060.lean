import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk060

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362451475653568713, 362451476085140535⟩, ⟨166960048117545325, 166961802179621285⟩, true⟩

def state01 : KState := ⟨⟨362384830439395798, 362384830872457067⟩, ⟨567075014026297163, 567076777032838931⟩, true⟩

def words00 : List Nat := [371279310447818653, 371279310447985732, 371279285640836157, 371279256545542778, 371279227459877346, 371279206756860810, 371279182874207747, 371279184722310439, 371279186409227746, 371279186409400967]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 6000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 6000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362536673283218361, 362536673717795228⟩, ⟨(-346039031932668673), (-346037259809724067)⟩, true⟩

def words01 : List Nat := [371279182562453260, 371279194408794641, 371279217497930769, 371279217498098505, 371279211037600038, 371279200035729212, 371279191458673516, 371279191458858521, 371279192445211799, 371279201992199858]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 6010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 6000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362384883775521767, 362384884211613334⟩, ⟨567818703132362131, 567820484381653425⟩, true⟩

def words02 : List Nat := [371279209960771222, 371279209960939194, 371279181345432571, 371279172530674506, 371279163718759102, 371279162683837422, 371279133470370534, 371279096557668040, 371279059657143063, 371279050129421237]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 6020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 6000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362278584357239101, 362278584794845839⟩, ⟨1210164850897089015, 1210166641290656879⟩, true⟩

def words03 : List Nat := [371279038384443155, 371279042251902644, 371279045979134195, 371279045979305224, 371279027261771493, 371279010062185741, 371279002973672058, 371279002973840437, 371278976687566825, 371278943510291312]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 6030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 6000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362438765842174431, 362438766281293505⟩, ⟨242056624504705356, 242058424040223854⟩, true⟩

def words04 : List Nat := [371278910343926116, 371278888406440714, 371278856766485437, 371278852367627668, 371278847970175219, 371278842553349602, 371278800848591824, 371278786350204399, 371278775937983837, 371278775938159658]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 6040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 6000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362512667959969796, 362512668400621847⟩, ⟨(-205270433589945425), (-205268624771906987)⟩, true⟩

def words05 : List Nat := [371278769326212400, 371278762652911487, 371278776444931565, 371278783400644123, 371278791309605097, 371278799216018322, 371278807425326034, 371278807425495787, 371278795690056770, 371278801278897395]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 6050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 6000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362380116948939585, 362380117391100506⟩, ⟨598822674187259085, 598824492156930195⟩, true⟩

def words06 : List Nat := [371278812379453398, 371278812379625425, 371278801244844409, 371278788371464589, 371278775502263429, 371278770739634076, 371278761085722540, 371278769776885130, 371278770519781499, 371278770519956673]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 6060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 6000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362612285003022522, 362612285446716989⟩, ⟨(-811709080505795752), (-811707253220002992)⟩, true⟩

def words07 : List Nat := [371278755917640520, 371278757564768916, 371278786199157844, 371278786199327337, 371278778857363224, 371278767217601962, 371278763975644569, 371278763975831065, 371278780964086662, 371278802918642659]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 6070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 6000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362436201056310963, 362436201501537625⟩, ⟨258773477101627404, 258775313711026638⟩, true⟩

def words08 : List Nat := [371278824742038040, 371278824742207676, 371278810690298153, 371278799520831642, 371278788354952317, 371278785254411852, 371278755624288517, 371278725907451743, 371278696200305825, 371278693342869485]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 6080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 6000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362279441146856238, 362279441593612408⟩, ⟨1215364664158866568, 1215366510090903834⟩, true⟩

def words09 : List Nat := [371278706227157129, 371278726081161238, 371278746259016872, 371278746259188146, 371278743245076612, 371278742690161475, 371278746252823714, 371278746252994038, 371278714672630984, 371278682005102721]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 6090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 6000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 6000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk060
