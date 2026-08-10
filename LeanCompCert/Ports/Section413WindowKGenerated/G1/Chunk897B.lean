import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk897A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk897B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk897A

def state06 : KState := ⟨⟨362478800443697828, 362478922333716236⟩, ⟨550258501141621751, 557645618095851553⟩, true⟩

def words05 : List Nat := [371285135603023705, 371285135476116792, 371285135347893664, 371285135345113719, 371285135295445345, 371285135270359758, 371285135244260106, 371285135219535370, 371285135028401705, 371285134963151351]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 89750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 89700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471412434456657, 362471534352368033⟩, ⟨1213435614340970609, 1220825235115480555⟩, true⟩

def words06 : List Nat := [371285134896098728, 371285134881510445, 371285134721859034, 371285134563049796, 371285134403083217, 371285134266666075, 371285134066561559, 371285133991843362, 371285133915983710, 371285133831426912]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 89760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 89700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484306498876052, 362484428445047349⟩, ⟨55850457132005285, 63242614942073685⟩, true⟩

def words07 : List Nat := [371285133682074145, 371285133597608148, 371285133535357496, 371285133538489100, 371285133399449074, 371285133239511177, 371285133078263786, 371285132996737702, 371285132867035105, 371285132862678694]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 89770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 89700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479085697052030, 362479207671492126⟩, ⟨524616643740305257, 532011339664604247⟩, true⟩

def words08 : List Nat := [371285132857173526, 371285132852358262, 371285132836405244, 371285132893166484, 371285132986160801, 371285132989292659, 371285132917129627, 371285132844651031, 371285132770964772, 371285132733744767]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 89780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 89700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475697770985094, 362475819773667890⟩, ⟨828872146513024066, 836269378490589266⟩, true⟩

def words09 : List Nat := [371285132686402409, 371285132706362570, 371285132708741899, 371285132702928286, 371285132601901751, 371285132540311899, 371285132535625087, 371285132538758279, 371285132450417936, 371285132350265781]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 89790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 89700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 89700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk897B
