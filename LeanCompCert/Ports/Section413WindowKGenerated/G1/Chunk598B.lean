import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk598A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk598B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk598A

def state06 : KState := ⟨⟨362467498172513601, 362467550700331590⟩, ⟨1051154032825739212, 1053277963233826482⟩, true⟩

def words05 : List Nat := [371285146363823215, 371285146669103795, 371285146966478812, 371285146968503889, 371285146900918193, 371285146910787293, 371285146971445570, 371285146973470777, 371285146681356233, 371285146389660589]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 59850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 59800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483416468213140, 362483469014156354⟩, ⟨98286785456142833, 100411800934078887⟩, true⟩

def words06 : List Nat := [371285146097093096, 371285146037502244, 371285145996821733, 371285146117831443, 371285146210196541, 371285146212223186, 371285146002123774, 371285146025384441, 371285146175930282, 371285146178026975]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 59860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 59800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495390374627938, 362495442939067347⟩, ⟨(-618695723732674070), (-616569600793305090)⟩, true⟩

def words07 : List Nat := [371285146151554849, 371285146075296217, 371285146061490509, 371285146063728796, 371285146046183354, 371285146080616570, 371285146115084730, 371285146117156997, 371285146183019926, 371285146357500685]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 59870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 59800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487616597494605, 362487669179966329⟩, ⟨(-153145997587772714), (-151018794779253044)⟩, true⟩

def words08 : List Nat := [371285146779701315, 371285146868033173, 371285146954592515, 371285147041829038, 371285147091147334, 371285147093402879, 371285147193976489, 371285147385473323, 371285147575016812, 371285147619217982]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 59880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 59800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493945922962150, 362493998523748893⟩, ⟨(-532239164156501306), (-530110864369449618)⟩, true⟩

def words09 : List Nat := [371285147776517439, 371285147934876080, 371285148322997455, 371285148339993382, 371285148341587035, 371285148274654764, 371285148385620954, 371285148441384116, 371285148590531246, 371285148740533764]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 59890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 59800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 59800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk598B
