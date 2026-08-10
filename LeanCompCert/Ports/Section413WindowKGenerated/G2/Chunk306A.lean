import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk306A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360553519282698303, 360553524924109304⟩, ⟨914551970731088587, 914668713130080263⟩, true⟩

def state01 : KState := ⟨⟨360590363556103992, 360590369201340900⟩, ⟨(-213005795613784480), (-212888936122603450)⟩, true⟩

def words00 : List Nat := [360583415082051648, 360583414986709441, 360583414987071630, 360583414529758450, 360583414072402002, 360583413345216829, 360583413759748270, 360583414364490242, 360583414364856566, 360583414546604936]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 30600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 30600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580767682024498, 360580773331105174⟩, ⟨80536635183211135, 80653612350896647⟩, true⟩

def words01 : List Nat := [360583414748505706, 360583414950506504, 360583414950838046, 360583414950543049, 360583413887275056, 360583411890112817, 360583409893004077, 360583408253558583, 360583407434095662, 360583407348490899]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 30610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 30600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360542927241946910, 360542932894899476⟩, ⟨1239139414174122935, 1239256509917972093⟩, true⟩

def words02 : List Nat := [360583407262833431, 360583406515906603, 360583405090768878, 360583404488783071, 360583403886732175, 360583402558409406, 360583400168019518, 360583397102018653, 360583394036137293, 360583391808053834]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 30620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 30600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360507306029015181, 360507311685803181⟩, ⟨2330622931861058183, 2330740145103565011⟩, true⟩

def words03 : List Nat := [360583390487534365, 360583390228282887, 360583389968997079, 360583389179794051, 360583388250422279, 360583386600415005, 360583384950391589, 360583384361305570, 360583382710712676, 360583380228397945]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 30630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 30600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360609300415733896, 360609306076362202⟩, ⟨(-795063414911926122), (-794946083983335748)⟩, true⟩

def words04 : List Nat := [360583377746154968, 360583375575493733, 360583373941060165, 360583373367198337, 360583372793345869, 360583371268502756, 360583370293201851, 360583369784045080, 360583369825239637, 360583370671840871]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 30640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 30600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk306A
