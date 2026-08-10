import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk626A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362507069065493091, 362507126715852654⟩, ⟨(-1361783569936907359), (-1359345929714204547)⟩, true⟩

def state01 : KState := ⟨⟨362494297734200386, 362494355403767094⟩, ⟨(-562300099963209806), (-559861257277271380)⟩, true⟩

def words00 : List Nat := [371285412531162506, 371285412533287970, 371285412699250371, 371285412911669684, 371285413187085295, 371285413189213841, 371285413189469890, 371285413170493342, 371285413359220517, 371285413504463821]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 62600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 62600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476191226282215, 362476248914939033⟩, ⟨571466924055107173, 573906962072307209⟩, true⟩

def words01 : List Nat := [371285413743897095, 371285413984178415, 371285414222790830, 371285414224916649, 371285414123476301, 371285414036948643, 371285414115365572, 371285414117491598, 371285413973685910, 371285413829695857]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 62610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 62600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476870211880273, 362476927919601027⟩, ⟨529008086750285294, 531449318646191578⟩, true⟩

def words02 : List Nat := [371285413706391876, 371285413708798630, 371285413705761800, 371285413770993029, 371285413789164650, 371285413791290886, 371285413500403893, 371285413465674765, 371285413456576953, 371285413458777879]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 62620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 62600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488867545777446, 362488925272915671⟩, ⟨(-222417361550726244), (-219974913445274306)⟩, true⟩

def words03 : List Nat := [371285413324897544, 371285413192785867, 371285413180398590, 371285413247431847, 371285413390702490, 371285413534803682, 371285413677176641, 371285413679303442, 371285413537887833, 371285413596642220]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 62630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 62600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468040708909309, 362468098455006615⟩, ⟨1082279911798266664, 1084723547598753172⟩, true⟩

def words04 : List Nat := [371285413853068798, 371285413855195661, 371285413772135040, 371285413627322510, 371285413481733820, 371285413294440104, 371285412992410364, 371285412820881898, 371285412648635729, 371285412478112741]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 62640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 62600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk626A
