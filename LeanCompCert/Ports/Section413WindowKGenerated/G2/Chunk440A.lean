import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk440A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360619146642195475, 360619158660593643⟩, ⟨(-1581994532419131131), (-1581637170441814245)⟩, true⟩

def state01 : KState := ⟨⟨360598158729941559, 360598170754072386⟩, ⟨(-658483344455717527), (-658125730213172585)⟩, true⟩

def words00 : List Nat := [360583213734298295, 360583214316587912, 360583215269275588, 360583216222097451, 360583216897721199, 360583217058523206, 360583217059058819, 360583216960402122, 360583216861643254, 360583217089529132]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 44000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 44000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567690200924286, 360567702230716043⟩, ⟨682587062332149200, 682944925740982372⟩, true⟩

def words01 : List Nat := [360583217507284238, 360583217925132205, 360583217984362683, 360583217984964153, 360583217718352556, 360583217319937156, 360583217037868060, 360583217038472285, 360583217006115701, 360583216654290350]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 44010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 44000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360628334271446981, 360628346306924301⟩, ⟨(-1987358723559317131), (-1987000609844854205)⟩, true⟩

def words02 : List Nat := [360583216465426459, 360583217100463444, 360583217546263637, 360583217992149321, 360583217992704528, 360583217987631230, 360583217468096434, 360583217464168432, 360583217970839403, 360583218996396608]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 44020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 44000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360608547835279350, 360608559876479942⟩, ⟨(-1116078881151147988), (-1115720515412275798)⟩, true⟩

def words03 : List Nat := [360583219701349624, 360583220406334090, 360583221188740975, 360583222296664686, 360583223272612242, 360583224248613732, 360583224814727578, 360583225046736978, 360583225622492194, 360583226198420582]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 44030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 44000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360614120615201381, 360614132662069703⟩, ⟨(-1361494693082530135), (-1361136077708526729)⟩, true⟩

def words04 : List Nat := [360583227289195864, 360583228258701285, 360583228933913767, 360583229609178617, 360583230004707098, 360583230657236337, 360583231479153010, 360583232301146332, 360583232863995265, 360583233566073959]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 44040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 44000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk440A
