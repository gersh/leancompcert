import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk352A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360538074219979604, 360538081772746093⟩, ⟨1545309888410944353, 1545489624381697675⟩, true⟩

def state01 : KState := ⟨⟨360571575746068437, 360571583303296368⟩, ⟨365870287424899975, 366050180460731209⟩, true⟩

def words00 : List Nat := [360581986481073213, 360581986040240742, 360581986002897197, 360581985762250420, 360581985521578185, 360581984593234888, 360581983256824028, 360581981804038682, 360581980351192427, 360581979502684631]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 35200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 35200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360532163993838477, 360532171555560771⟩, ⟨1753766644012467713, 1753946695317070067⟩, true⟩

def words01 : List Nat := [360581979207853938, 360581978235941837, 360581977263995126, 360581976660874480, 360581976460692402, 360581976058667329, 360581975656626449, 360581974582493520, 360581972704836860, 360581971291373295]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 35210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 35200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580129403080211, 360580136969252539⟩, ⟨64154917785844729, 64335125842694651⟩, true⟩

def words02 : List Nat := [360581969877833683, 360581969269404507, 360581968543931392, 360581967347428976, 360581966150908221, 360581964731080964, 360581963825089917, 360581963723982502, 360581963622829251, 360581963115316766]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 35220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 35200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360604436155691488, 360604443726327365⟩, ⟨(-792503057518335819), (-792322692188848109)⟩, true⟩

def words03 : List Nat := [360581963063872125, 360581962976511614, 360581962917645811, 360581962918118479, 360581962419913962, 360581961218292864, 360581960016648909, 360581959469597770, 360581960108012237, 360581960746497371]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 35230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 35200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360551963553950258, 360551971129087096⟩, ⟨1056634556947307917, 1056815080911935483⟩, true⟩

def words04 : List Nat := [360581960829502062, 360581960829974871, 360581960389620390, 360581960184623969, 360581959979513610, 360581959127398489, 360581957473103473, 360581955359184589, 360581953245295222, 360581951698758357]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 35240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 35200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk352A
