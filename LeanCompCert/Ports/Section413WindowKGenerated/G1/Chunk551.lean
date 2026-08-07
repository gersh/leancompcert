import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk551

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489859322161790, 362489903535478069⟩, ⟨(-276555217400052068), (-274909498806518954)⟩, true⟩

def state01 : KState := ⟨⟨362481320867831193, 362481365097869576⟩, ⟨193881379140662914, 195528019204323518⟩, true⟩

def words00 : List Nat := [371284914435369841, 371284914437222698, 371284914090881651, 371284914074559121, 371284914111005398, 371284914112858743, 371284913774948304, 371284913426125152, 371284913076575501, 371284913056846247]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 55100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 55100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479922511351813, 362479966758111673⟩, ⟨270965993832738245, 272613555501142527⟩, true⟩

def words01 : List Nat := [371284913065710609, 371284913139698659, 371284913213556451, 371284913215414915, 371284912953944510, 371284912772663718, 371284912735800558, 371284912737687875, 371284912664946225, 371284912577333392]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 55110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 55100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362493659241406540, 362493703504728831⟩, ⟨(-486247575864590228), (-484599101188591458)⟩, true⟩

def words02 : List Nat := [371284912567751504, 371284912569794098, 371284912712890863, 371284912942543966, 371284913090226141, 371284913092080737, 371284912951189275, 371284913046720264, 371284913386697989, 371284913548058563]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 55120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 55100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487370609028638, 362487414889255190⟩, ⟨(-139497988157116777), (-137848581462718031)⟩, true⟩

def words03 : List Nat := [371284913642507600, 371284913737603889, 371284914050642256, 371284914201794353, 371284914452501062, 371284914703934117, 371284914955244607, 371284914957102962, 371284914912706218, 371284914960319141]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 55130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 55100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480778785647485, 362480823082387471⟩, ⟨224022015576514626, 225672332907062304⟩, true⟩

def words04 : List Nat := [371284915283363643, 371284915285218420, 371284915213406950, 371284915071674050, 371284914929220527, 371284914833405641, 371284914780449035, 371284914919574423, 371284915053863362, 371284915055785605]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 55140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 55100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362507986892111664, 362508031205667553⟩, ⟨(-1276627843673240802), (-1274976598862334718)⟩, true⟩

def words05 : List Nat := [371284915202352528, 371284915424113512, 371284915781198035, 371284915921965974, 371284916009651315, 371284916097893687, 371284916429220032, 371284916631681398, 371284917051992217, 371284917473159761]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478279502182434, 362478323832473751⟩, ⟨362136488723921012, 363788656747673100⟩, true⟩

def words06 : List Nat := [371284917875704320, 371284917877559800, 371284918133976514, 371284918427864505, 371284918649633689, 371284918651489350, 371284918435738760, 371284918130721210, 371284917824934558, 371284917790362961]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478179240862709, 362478223587844265⟩, ⟨367759440446074610, 369412529354108348⟩, true⟩

def words07 : List Nat := [371284917880709696, 371284918091314276, 371284918285253816, 371284918287142521, 371284918228705362, 371284918249619448, 371284918505931707, 371284918507788252, 371284918388678230, 371284918269420092]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482130182794427, 362482174546418806⟩, ⟨149770856294739857, 151424863637068519⟩, true⟩

def words08 : List Nat := [371284918164460964, 371284918166511756, 371284918225831657, 371284918404974705, 371284918561618393, 371284918563475576, 371284918339636610, 371284918213322948, 371284918245595953, 371284918247517503]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489234119082734, 362489278499634708⟩, ⟨(-242323193224674777), (-240668251564895291)⟩, true⟩

def words09 : List Nat := [371284918199192836, 371284918152098426, 371284918321754138, 371284918376937331, 371284918452885869, 371284918529499481, 371284918604755053, 371284918606633370, 371284918565208363, 371284918646523988]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk551
