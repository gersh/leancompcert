import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk739A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk739B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk739A

def state06 : KState := ⟨⟨362472426445559677, 362472507974674905⟩, ⟨941081928477652839, 945154056700073075⟩, true⟩

def words05 : List Nat := [371285287241271210, 371285287448480940, 371285287622086796, 371285287624629064, 371285287574195012, 371285287533012368, 371285287567036750, 371285287569579026, 371285287404408278, 371285287234500488]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 73950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 73900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478558610688819, 362478640162611698⟩, ⟨487587878853346890, 491661694043544840⟩, true⟩

def words06 : List Nat := [371285287073215485, 371285287076092502, 371285287105537199, 371285287192794718, 371285287249039968, 371285287251584389, 371285287101127397, 371285287020605487, 371285286938758169, 371285286934195361]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 73960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 73900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480126492734621, 362480208067792945⟩, ⟨371628114699680134, 375703641336750626⟩, true⟩

def words07 : List Nat := [371285286846257282, 371285286758070555, 371285286760454431, 371285286763377874, 371285286769413702, 371285286776480586, 371285286783025518, 371285286785569196, 371285286582074513, 371285286516580952]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 73970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 73900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481369875165996, 362481451472915014⟩, ⟨279638581466072151, 283715786875534767⟩, true⟩

def words08 : List Nat := [371285286548073213, 371285286550616531, 371285286430878123, 371285286284861910, 371285286137830990, 371285286047663771, 371285285932575783, 371285285959979498, 371285285985533073, 371285285988212697]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 73980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 73900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490521773868675, 362490603394619219⟩, ⟨(-397551548262570057), (-393472640854106217)⟩, true⟩

def words09 : List Nat := [371285286015914163, 371285286096776617, 371285286331131179, 371285286333674711, 371285286324960943, 371285286286866415, 371285286247791038, 371285286230791666, 371285286193872732, 371285286268622894]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 73990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 73900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 73900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk739B
