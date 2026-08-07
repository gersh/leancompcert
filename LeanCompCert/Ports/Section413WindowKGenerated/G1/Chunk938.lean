import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk938

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486900483376022, 362487034046233622⟩, ⟨(-184665680423168689), (-176207041600961017)⟩, true⟩

def state01 : KState := ⟨⟨362480615411306588, 362480749003774752⟩, ⟨404858566429641758, 413319982872633552⟩, true⟩

def words00 : List Nat := [371285155548630385, 371285155551914148, 371285155422474568, 371285155377760217, 371285155331457286, 371285155315964530, 371285155208158660, 371285155078151178, 371285154946722136, 371285154930465645]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 93800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 93800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477539252500579, 362477672874478260⟩, ⟨693509873643662601, 701974058529854651⟩, true⟩

def words01 : List Nat := [371285154952407075, 371285155022622373, 371285155091540569, 371285155094882394, 371285155069173440, 371285155067777520, 371285155140857348, 371285155144142557, 371285155087198356, 371285155011107229]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 93810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 93800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484168738288022, 362484302389715332⟩, ⟨71482875498595716, 79949823498468328⟩, true⟩

def words02 : List Nat := [371285154933634872, 371285154885412862, 371285154791574227, 371285154770712982, 371285154748810562, 371285154709964365, 371285154537607898, 371285154480604386, 371285154457307870, 371285154460732049]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 93820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 93800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485530638944206, 362485664320308893⟩, ⟨(-56294905336425402), (-47825148168100100)⟩, true⟩

def words03 : List Nat := [371285154454105920, 371285154448411140, 371285154532387968, 371285154585455757, 371285154641702546, 371285154699136960, 371285154756266046, 371285154759551433, 371285154670520859, 371285154680085877]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 93830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 93800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475158345046228, 362475292055684167⟩, ⟨917115426215864167, 925587930541583707⟩, true⟩

def words04 : List Nat := [371285154727508640, 371285154730851540, 371285154684081645, 371285154638722063, 371285154592130493, 371285154575433645, 371285154500701827, 371285154502503404, 371285154503209148, 371285154473697397]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 93840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 93800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491005789682290, 362491139530013811⟩, ⟨(-570233740960982535), (-561758449748481911)⟩, true⟩

def words05 : List Nat := [371285154379302623, 371285154391730518, 371285154504145219, 371285154507431166, 371285154481559060, 371285154438997855, 371285154420347996, 371285154423969457, 371285154458675926, 371285154526127762]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469670729747351, 362469804499762675⟩, ⟨1432345842107843358, 1440823919593453988⟩, true⟩

def words06 : List Nat := [371285154592747375, 371285154596033902, 371285154525188420, 371285154455978545, 371285154385114193, 371285154349794513, 371285154162382980, 371285153969953238, 371285153776218628, 371285153641337124]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362466569632405770, 362466703432020222⟩, ⟨1723525426338660138, 1732006282448348238⟩, true⟩

def words07 : List Nat := [371285153480051984, 371285153433650975, 371285153386111297, 371285153332181225, 371285153201494175, 371285153106095767, 371285153009068518, 371285152960195979, 371285152775674610, 371285152582877150]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484153794157480, 362484287623201994⟩, ⟨72647878489134737, 81131497640774115⟩, true⟩

def words08 : List Nat := [371285152388589106, 371285152297924930, 371285152149258416, 371285152101355005, 371285152052412757, 371285151966397851, 371285151794459501, 371285151737769847, 371285151732031257, 371285151735435893]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487271299171587, 362487405158157156⟩, ⟨(-220071660632933501), (-211585230163600641)⟩, true⟩

def words09 : List Nat := [371285151728738951, 371285151688826271, 371285151717596755, 371285151734608744, 371285151774318812, 371285151815342259, 371285151855610042, 371285151858962349, 371285151850280244, 371285151878318139]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk938
