import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk451

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362461801973749033, 362461831119046900⟩, ⟨1069460606876224007, 1070348716098615925⟩, true⟩

def state01 : KState := ⟨⟨362465375949135751, 362465405107815318⟩, ⟨908216798512795629, 909105511318096637⟩, true⟩

def words00 : List Nat := [371285563381362818, 371285562940106570, 371285562253237841, 371285561790882373, 371285561328065281, 371285560776864103, 371285559718381875, 371285559066149346, 371285558413142692, 371285558189422902]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 45100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 45100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471133790341915, 362471162962623431⟩, ⟨648443613153500963, 649332939611198289⟩, true⟩

def words01 : List Nat := [371285557743802874, 371285557198430802, 371285556652463656, 371285556550274028, 371285556233440456, 371285555938129722, 371285555642354052, 371285555332890079, 371285554523942588, 371285554206852403]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 45110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 45100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480841161820986, 362480870347423509⟩, ⟨210501694317708013, 211391621888232631⟩, true⟩

def words02 : List Nat := [371285554060926419, 371285554062456086, 371285553970638439, 371285553863320442, 371285553762659634, 371285553764322966, 371285553887845941, 371285554196135085, 371285554405746415, 371285554407292515]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 45120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 45100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362510409614435318, 362510438813523433⟩, ⟨(-1124090277096720547), (-1123199740853752549)⟩, true⟩

def words03 : List Nat := [371285554691503084, 371285555080240876, 371285555705711020, 371285555707204872, 371285555678698621, 371285555494882398, 371285555615578626, 371285555677836579, 371285556230094182, 371285556782977948]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 45130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 45100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362466962492057307, 362466991704649322⟩, ⟨837272050520831271, 838163196394629355⟩, true⟩

def words04 : List Nat := [371285557283982797, 371285557285476916, 371285557182827323, 371285557235019537, 371285557435155898, 371285557436650097, 371285556983079851, 371285556481983855, 371285555980323197, 371285555673561717]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 45140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 45100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362441628560967073, 362441657787008926⟩, ⟨1981333406752895941, 1982225159955311577⟩, true⟩

def words05 : List Nat := [371285555283666990, 371285555305556513, 371285555306685585, 371285555289591862, 371285554682446889, 371285554090543599, 371285553497926820, 371285553110208506, 371285552139929838, 371285551169647441]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 45150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 45100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362464154299444956, 362464183538874029⟩, ⟨964057489279510514, 964949847117782400⟩, true⟩

def words06 : List Nat := [371285550198730797, 371285549718663814, 371285549056561077, 371285548754357272, 371285548451688197, 371285548072874879, 371285547254416523, 371285546790243357, 371285546325300475, 371285546165553635]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 45160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 45100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470281176658538, 362470310429714308⟩, ⟨687261814778413728, 688154788203899958⟩, true⟩

def words07 : List Nat := [371285545693774807, 371285545114995972, 371285544535646976, 371285544399429078, 371285544018490388, 371285543719683696, 371285543420381508, 371285542993938553, 371285542168012607, 371285541832729003]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 45170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 45100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473798561196788, 362473827827569701⟩, ⟨528408041129503429, 529301616292178679⟩, true⟩

def words08 : List Nat := [371285541649267283, 371285541650767631, 371285541446773744, 371285541242620300, 371285541037901380, 371285540854868666, 371285540522531984, 371285540576786862, 371285540630099795, 371285540631647864]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 45180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 45100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496398945814972, 362496428225739564⟩, ⟨(-492940885041826324), (-492046697411766170)⟩, true⟩

def words09 : List Nat := [371285540603825462, 371285540835995086, 371285541472008979, 371285541524008974, 371285541525168538, 371285541452023661, 371285541792932336, 371285541993271330, 371285542235157023, 371285542477693907]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 45190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 45100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 45100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk451
