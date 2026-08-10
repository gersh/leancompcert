import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk881A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360599131328078688, 360599182262130230⟩, ⟨(-1500605301406041195), (-1497575048208147307)⟩, true⟩

def state01 : KState := ⟨⟨360586812083388250, 360586863029556463⟩, ⟨(-415240368465281128), (-412209047733096794)⟩, true⟩

def words00 : List Nat := [360582183983894648, 360582184152363860, 360582184377187998, 360582184602377709, 360582184774549475, 360582184818219998, 360582184819351209, 360582184788218338, 360582184756861285, 360582184736860511]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 88100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 88100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567666794347313, 360567717752459302⟩, ⟨1271761537828107958, 1274793910987908628⟩, true⟩

def words01 : List Nat := [360582184790036235, 360582184843451037, 360582184844583595, 360582184815320388, 360582184748819806, 360582184650321429, 360582184580154511, 360582184581423990, 360582184482621702, 360582184319765112]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 88110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 88100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579811084343290, 360579862054458614⟩, ⟨201489853935116579, 204523284888362367⟩, true⟩

def words02 : List Nat := [360582184156631180, 360582184013750324, 360582183948655452, 360582183880761410, 360582183812772044, 360582183633439234, 360582183352545547, 360582183110443930, 360582182867956500, 360582182754389267]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 88120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 88100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574824879743412, 360574875861943900⟩, ⟨640952499925434890, 643986996003454236⟩, true⟩

def words03 : List Nat := [360582182729188960, 360582182624288687, 360582182519139608, 360582182549595404, 360582182574824058, 360582182600261214, 360582182601422903, 360582182525757314, 360582182353595846, 360582182272154968]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 88130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 88100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569846359176693, 360569897353329942⟩, ⟨1079714764938809063, 1082750314592276331⟩, true⟩

def words04 : List Nat := [360582182190288959, 360582182165295972, 360582182011566138, 360582181759981541, 360582181508176412, 360582181170118749, 360582180911232284, 360582180761385688, 360582180611403968, 360582180397171035]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 88140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 88100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk881A
