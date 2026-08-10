import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk623A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk623B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk623A

def state06 : KState := ⟨⟨362508732495364647, 362508789687223908⟩, ⟨(-1459540263618417249), (-1457131270565161121)⟩, true⟩

def words05 : List Nat := [371285421081433809, 371285421394988020, 371285421891297181, 371285422045430398, 371285422160315760, 371285422275883351, 371285422621367362, 371285422867515736, 371285423243669675, 371285423620763057]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 62350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 62300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485100595821842, 362485157806822548⟩, ⟨14179146214626020, 16589333023978776⟩, true⟩

def words06 : List Nat := [371285423976954145, 371285423990901364, 371285424071370009, 371285424152884693, 371285424310860562, 371285424312977566, 371285424128344331, 371285423943428825, 371285423786896045, 371285423789394682]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 62360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 62300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362466313060880217, 362466370290894749⟩, ⟨1186148757783263112, 1188560130583299804⟩, true⟩

def words07 : List Nat := [371285423996749214, 371285424209205325, 371285424390041104, 371285424392168423, 371285424338934923, 371285424352763597, 371285424415975857, 371285424418093129, 371285424138880040, 371285423835790282]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 62370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 62300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474544624607913, 362474601873573241⟩, ⟨672639306950139532, 675051861998763326⟩, true⟩

def words08 : List Nat := [371285423531798307, 371285423329770957, 371285423010220046, 371285422948757419, 371285422886569298, 371285422786172857, 371285422342622160, 371285422069024551, 371285421794338102, 371285421746341293]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 62380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 62300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479624136827714, 362479681405142508⟩, ⟨355702327706039122, 358116090061616516⟩, true⟩

def words09 : List Nat := [371285421574531510, 371285421355523029, 371285421135626154, 371285421126674325, 371285420988995860, 371285420929593120, 371285420869507756, 371285420808777757, 371285420534349404, 371285420445047342]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 62390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 62300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 62300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk623B
