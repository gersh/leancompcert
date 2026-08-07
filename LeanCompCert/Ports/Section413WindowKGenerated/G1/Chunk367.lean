import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk367

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362466607399646016, 362466626378083042⟩, ⟨668761536123094937, 669232242705282795⟩, true⟩

def state01 : KState := ⟨⟨362457656193550696, 362457675182707379⟩, ⟨997340522580258435, 997811622627276645⟩, true⟩

def words00 : List Nat := [371284861093023194, 371284860873824583, 371284860282258410, 371284860113229617, 371284859943819836, 371284859661753451, 371284858390512492, 371284857381414846, 371284856371737428, 371284856104053805]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 36700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 36700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362475679321851025, 362475698321924835⟩, ⟨335640623862061058, 336112124729558398⟩, true⟩

def words01 : List Nat := [371284855364553722, 371284854628703835, 371284853896721325, 371284853898040037, 371284853611809092, 371284853362758013, 371284853113327571, 371284852861782217, 371284851949993544, 371284851702227928]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 36710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 36700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362470730358123898, 362470749368860127⟩, ⟨517536591052703952, 518008483500710814⟩, true⟩

def words02 : List Nat := [371284851945612846, 371284851946830806, 371284851931417031, 371284851914078316, 371284852032331536, 371284852033649620, 371284852112231393, 371284852423768272, 371284852511740735, 371284852512979395]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 36720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 36700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362510130491257889, 362510149512807308⟩, ⟨(-929851207230886354), (-929378917560469930)⟩, true⟩

def words03 : List Nat := [371284852274145020, 371284852419865040, 371284853222971410, 371284853224168445, 371284853040061435, 371284852794020304, 371284852766901094, 371284852768238180, 371284853405924847, 371284854095764755]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 36730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 36700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478498499162635, 362478517531511529⟩, ⟨232307268991747548, 232779955490412038⟩, true⟩

def words04 : List Nat := [371284854708816154, 371284854710013497, 371284854336103934, 371284854130173702, 371284853940807806, 371284853942007809, 371284853198600488, 371284852445850621, 371284851692666101, 371284851679960248]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 36740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 36700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362445258368855463, 362445277411989243⟩, ⟨1454153511239443621, 1454626594138817005⟩, true⟩

def words05 : List Nat := [371284851539832965, 371284851572549680, 371284851602456642, 371284851603659615, 371284851104559641, 371284850830622916, 371284850556096063, 371284850468995249, 371284849395566178, 371284848320426099]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 36750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 36700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487008648751351, 362487027702610318⟩, ⟨(-80708324669995071), (-80234847458145785)⟩, true⟩

def words06 : List Nat := [371284847244801846, 371284846909092436, 371284846313123985, 371284846320273891, 371284846321211833, 371284846266699052, 371284845384162753, 371284845241419061, 371284845627737995, 371284845688320303]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 36760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 36700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491976462910082, 362491995527684398⟩, ⟨(-263465580523774657), (-262991701898746389)⟩, true⟩

def words07 : List Nat := [371284845689234146, 371284845519144893, 371284845550034607, 371284845551368139, 371284845452020561, 371284845512290810, 371284845513192728, 371284845475412985, 371284845126489285, 371284845322363751]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 36770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 36700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486847160768369, 362486866236215455⟩, ⟨(-74760671349904230), (-74286400125000356)⟩, true⟩

def words08 : List Nat := [371284846256069513, 371284846321153137, 371284846322058014, 371284846291125048, 371284846265137003, 371284846266457505, 371284846281430626, 371284846658979606, 371284847034095405, 371284847090225268]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 36780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 36700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362515429218855080, 362515448305167923⟩, ⟨(-1126360303834260823), (-1125885632805229887)⟩, true⟩

def words09 : List Nat := [371284847884120913, 371284848678642549, 371284850210613688, 371284850758729284, 371284851040283881, 371284851322179365, 371284852221200876, 371284852753288454, 371284853585517586, 371284854418240796]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 36790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 36700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 36700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk367
