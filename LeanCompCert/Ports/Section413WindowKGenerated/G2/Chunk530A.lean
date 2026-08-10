import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk530A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360596905865622714, 360596923571448508⟩, ⟨(-793513711743391267), (-792879656172709147)⟩, true⟩

def state01 : KState := ⟨⟨360575629782425399, 360575647495255710⟩, ⟨334121354379415871, 334755781222904475⟩, true⟩

def words00 : List Nat := [360581963910972373, 360581963911707176, 360581963657555732, 360581963708624928, 360581963709239874, 360581963670868996, 360581963515060739, 360581963181121670, 360581962847058679, 360581962450570234]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 53000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 53000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360555922531084033, 360555940250843182⟩, ⟨1378875715386073555, 1379510509562241979⟩, true⟩

def words01 : List Nat := [360581962332049367, 360581962204929684, 360581962077734217, 360581961724762479, 360581961269798861, 360581960624923140, 360581959979856039, 360581959690021448, 360581959422629822, 360581958932653108]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 53010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 53000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360563861549866771, 360563879276558715⟩, ⟨957942603726968230, 958577765514685148⟩, true⟩

def words02 : List Nat := [360581958442523643, 360581958153382624, 360581958050716218, 360581958059246685, 360581958059937027, 360581957720324951, 360581957025847987, 360581956437547541, 360581955849046807, 360581955417714942]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 53020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 53000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360549560960216067, 360549578693917264⟩, ⟨1716408054949289134, 1717043588472512410⟩, true⟩

def words03 : List Nat := [360581955077514343, 360581954468528426, 360581953859412026, 360581953545246186, 360581953409621440, 360581953184872625, 360581952960058275, 360581952521272913, 360581951920103194, 360581951310592840]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 53030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 53000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360559896964518931, 360559914705142477⟩, ⟨1168067865950106350, 1168703766669736528⟩, true⟩

def words04 : List Nat := [360581950700856501, 360581950092889865, 360581949430484313, 360581948590269620, 360581947749966653, 360581946786973550, 360581946102719497, 360581945773224488, 360581945443660091, 360581944936370936]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 53040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 53000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk530A
