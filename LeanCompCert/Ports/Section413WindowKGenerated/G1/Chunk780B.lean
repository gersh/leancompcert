import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk780A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk780B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk780A

def state06 : KState := ⟨⟨362491932382212752, 362492023581153038⟩, ⟨(-535000929228333759), (-530193605097962061)⟩, true⟩

def words05 : List Nat := [371285230658675512, 371285230712434640, 371285230908825330, 371285231024247139, 371285231173709320, 371285231324243168, 371285231434140944, 371285231436836537, 371285231448649827, 371285231538966826]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 78050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 78000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483365920345629, 362483457143287103⟩, ⟨133775884126327706, 138585081911888980⟩, true⟩

def words06 : List Nat := [371285231777599796, 371285231840569065, 371285231902870962, 371285231966177560, 371285232059225935, 371285232071998048, 371285232141281426, 371285232211624596, 371285232279242804, 371285232282033253]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 78060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 78000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501328441369289, 362501419688728656⟩, ⟨(-1268698353231376541), (-1263887249022260407)⟩, true⟩

def words07 : List Nat := [371285232278423890, 371285232298936449, 371285232458474350, 371285232461168697, 371285232419801453, 371285232348634594, 371285232349555989, 371285232395971042, 371285232605115092, 371285232815494166]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 78070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 78000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478378172947249, 362478469444584679⟩, ⟨523347393278273449, 528160393242028389⟩, true⟩

def words08 : List Nat := [371285233003967535, 371285233006661880, 371285233099330329, 371285233225492246, 371285233327147034, 371285233329841520, 371285233213062106, 371285233097238255, 371285232980309469, 371285232927658595]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 78080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 78000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467561679120016, 362467652975035800⟩, ⟨1368106509398018681, 1372921405383759335⟩, true⟩

def words09 : List Nat := [371285232864623290, 371285232889311798, 371285232912261350, 371285232914956293, 371285232719293444, 371285232575210183, 371285232429698539, 371285232407272647, 371285232216370365, 371285231994310881]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 78090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 78000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 78000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk780B
