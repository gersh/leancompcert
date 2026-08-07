import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk955

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478425183066687, 362478563823718106⟩, ⟨627099626914553416, 636038893238049860⟩, true⟩

def state01 : KState := ⟨⟨362489360571306629, 362489499241961481⟩, ⟨(-417279398104782406), (-408337266300495986)⟩, true⟩

def words00 : List Nat := [371285223849412410, 371285223828146853, 371285223791879446, 371285223821202016, 371285223832983764, 371285223836341422, 371285223764609566, 371285223786573301, 371285223903281504, 371285223951510115]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 95500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 95500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483227436882231, 362483366138037250⟩, ⟨168534865252737674, 177479910283005502⟩, true⟩

def words01 : List Nat := [371285224000445364, 371285224050526945, 371285224136730422, 371285224169760227, 371285224207622374, 371285224246695732, 371285224285071507, 371285224288419683, 371285224192551602, 371285224177299007]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 95510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 95500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483865589118079, 362484004320138222⟩, ⟨107598831009546286, 116546728910790958⟩, true⟩

def words02 : List Nat := [371285224231326205, 371285224234732931, 371285224217457978, 371285224188536396, 371285224159464472, 371285224163196812, 371285224194296310, 371285224267239335, 371285224318019468, 371285224321487650]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 95520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 95500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362501206838285150, 362501345599536181⟩, ⟨(-1549091514716974785), (-1540140728705535675)⟩, true⟩

def words03 : List Nat := [371285224407941058, 371285224508873167, 371285224707790243, 371285224781209111, 371285224825139154, 371285224870177971, 371285224986017961, 371285225048734176, 371285225219735410, 371285225392204193]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 95530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 95500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362499888586900849, 362500027378413275⟩, ⟨(-1423185748173836136), (-1414232070838278472)⟩, true⟩

def words04 : List Nat := [371285225562975183, 371285225642558473, 371285225766360697, 371285225891926469, 371285226040036955, 371285226106108312, 371285226170861327, 371285226236714947, 371285226410912853, 371285226569726414]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 95540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 95500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362478899869949913, 362479038691607053⟩, ⟨582442877980722761, 591399435801177077⟩, true⟩

def words05 : List Nat := [371285226789169723, 371285227010015154, 371285227229111665, 371285227302972525, 371285227398924871, 371285227496494697, 371285227583802721, 371285227587152381, 371285227528589507, 371285227467620042]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490513276635691, 362490652128286743⟩, ⟨(-527377448661654660), (-518418024471360790)⟩, true⟩

def words06 : List Nat := [371285227450022408, 371285227453748705, 371285227508372659, 371285227574336302, 371285227613092551, 371285227616442951, 371285227523247126, 371285227527653872, 371285227639883950, 371285227700118456]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491264786997604, 362491403669198047⟩, ⟨(-599201991319577372), (-590239647372510284)⟩, true⟩

def words07 : List Nat := [371285227722592252, 371285227746097400, 371285227859992387, 371285227930207836, 371285228032802771, 371285228136724647, 371285228239027854, 371285228251341502, 371285228318238369, 371285228387004175]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488278276853474, 362488417188875855⟩, ⟨(-313734431455253504), (-304769236974120840)⟩, true⟩

def words08 : List Nat := [371285228563485445, 371285228595077915, 371285228621097019, 371285228648299013, 371285228680453669, 371285228684146709, 371285228738726228, 371285228814982983, 371285228889149072, 371285228925995730]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499658061476746, 362499797003837973⟩, ⟨(-1401582381023092936), (-1392614286298710236)⟩, true⟩

def words09 : List Nat := [371285229030320375, 371285229136475909, 371285229341074609, 371285229400822752, 371285229443458940, 371285229487108189, 371285229638984256, 371285229750288577, 371285229904977980, 371285230061166885]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk955
