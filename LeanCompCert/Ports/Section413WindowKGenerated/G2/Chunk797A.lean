import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk797A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592439231508863, 360592480593222310⟩, ⟨(-820566659131550707), (-818340244471470259)⟩, true⟩

def state01 : KState := ⟨⟨360582121837506163, 360582163210085925⟩, ⟨1735245448431553, 3962526208374427⟩, true⟩

def words00 : List Nat := [360582213006168878, 360582213051660430, 360582213143687485, 360582213236055922, 360582213252513794, 360582213253661045, 360582213246166389, 360582213151280599, 360582213056195295, 360582212921868743]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 79700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 79700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360554960655297885, 360555002038609629⟩, ⟨2166934085986458501, 2169162222245234147⟩, true⟩

def words01 : List Nat := [360582213039067117, 360582213157104985, 360582213163971224, 360582213165110880, 360582213014878684, 360582212802701890, 360582212590174118, 360582212402255977, 360582212140695564, 360582211800554502]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 79710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 79700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570964934081992, 360571006328173276⟩, ⟨890962173039214947, 893191168694051103⟩, true⟩

def words02 : List Nat := [360582211460164492, 360582211206176996, 360582211050592564, 360582210891431772, 360582210732185365, 360582210440215789, 360582209991058058, 360582209654193779, 360582209316999328, 360582209026890121]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 79720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 79700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360555263449352085, 360555304854297132⟩, ⟨2142970405551160655, 2145200266630471925⟩, true⟩

def words03 : List Nat := [360582208887410142, 360582208669464226, 360582208451304767, 360582208347985487, 360582208344461822, 360582208264655240, 360582208184744193, 360582207984253029, 360582207626616328, 360582207290547828]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 79730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 79700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360557605987225005, 360557647402908543⟩, ⟨1956122799324147084, 1958353516744608340⟩, true⟩

def words04 : List Nat := [360582206954098176, 360582206691047305, 360582206381718587, 360582205975202743, 360582205568491735, 360582205087829159, 360582204685423769, 360582204336584701, 360582203987639760, 360582203559858319]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 79740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 79700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk797A
