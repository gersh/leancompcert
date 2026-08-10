import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk798A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk798B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk798A

def state06 : KState := ⟨⟨362480623833240071, 362480719453967043⟩, ⟨350931847886474825, 356088333053597079⟩, true⟩

def words05 : List Nat := [371285178422727016, 371285178373344508, 371285178404177076, 371285178410183992, 371285178463234143, 371285178517436324, 371285178568721349, 371285178571481530, 371285178413641062, 371285178361217902]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 79850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 79800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482732977962986, 362482828623282766⟩, ⟨182488611906591613, 187647061179516471⟩, true⟩

def words06 : List Nat := [371285178408094111, 371285178410854730, 371285178326929974, 371285178213645250, 371285178099280826, 371285178034218080, 371285177951551887, 371285177990581106, 371285178026423900, 371285178029332341]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 79860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 79800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488528237660661, 362488623907946570⟩, ⟨(-280406341845708106), (-275245898403871934)⟩, true⟩

def words07 : List Nat := [371285178033448478, 371285178068454434, 371285178258609201, 371285178261369740, 371285178242963476, 371285178199739825, 371285178174077213, 371285178177119531, 371285178162476014, 371285178208738951]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 79870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 79800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479122475183275, 362479218170383837⟩, ⟨470927801241032482, 476090234993698864⟩, true⟩

def words08 : List Nat := [371285178253832207, 371285178256611699, 371285178160959116, 371285178129952206, 371285178097531738, 371285178094695896, 371285177902898482, 371285177714209155, 371285177524364556, 371285177492389016]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 79880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 79800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472251753848180, 362472347473912348⟩, ⟨1019857358604222607, 1025021778837527749⟩, true⟩

def words09 : List Nat := [371285177419701627, 371285177398225365, 371285177375877969, 371285177322341001, 371285177085721321, 371285176875786512, 371285176664400650, 371285176598023875, 371285176439631457, 371285176282158125]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 79890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 79800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 79800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk798B
