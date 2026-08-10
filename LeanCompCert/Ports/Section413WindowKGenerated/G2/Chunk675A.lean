import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk675A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586099673561848, 360586128954312203⟩, ⟨(-219174860708195563), (-217839792264672995)⟩, true⟩

def state01 : KState := ⟨⟨360551823024987376, 360551852314724398⟩, ⟨2094622278693085935, 2095957953782407451⟩, true⟩

def words00 : List Nat := [360582901789691042, 360582901790644200, 360582901615311433, 360582901330388720, 360582901045320183, 360582900639642013, 360582900344067613, 360582899924622265, 360582899505080818, 360582898944168665]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 67500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 67500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584810471416237, 360584839770144135⟩, ⟨(-132561297598883184), (-131225015491206680)⟩, true⟩

def words01 : List Nat := [360582898485064256, 360582898245325966, 360582898005314214, 360582897945735173, 360582897667016499, 360582897182513999, 360582896697843370, 360582896387259003, 360582896270705065, 360582896300475570]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 67510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 67500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578820095696346, 360578849403519172⟩, ⟨271951247689872869, 273288143930737053⟩, true⟩

def words02 : List Nat := [360582896301325155, 360582896217399511, 360582896451514777, 360582896685905621, 360582896802729809, 360582896824180384, 360582896825039134, 360582896694586632, 360582896563972835, 360582896318133873]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 67520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 67500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360554981536018898, 360555010852819044⟩, ⟨1881965533208111159, 1883303035732949315⟩, true⟩

def words03 : List Nat := [360582896417995347, 360582896577961468, 360582896628237298, 360582896629190903, 360582896460456064, 360582896172377269, 360582895883998983, 360582895814721857, 360582895526394471, 360582895114526669]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 67530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 67500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567402375483770, 360567431701295298⟩, ⟨1042912370669557992, 1044250481867010710⟩, true⟩

def words04 : List Nat := [360582894702451203, 360582894266852978, 360582893941267463, 360582893611036192, 360582893280750736, 360582892767576857, 360582892035335590, 360582891522257413, 360582891008910305, 360582890627747808]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 67540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 67500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk675A
