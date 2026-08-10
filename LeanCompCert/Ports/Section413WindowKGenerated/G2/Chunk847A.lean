import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk847A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571078760333902, 360571125695924299⟩, ⟨956090668101596902, 958775406729232364⟩, true⟩

def state01 : KState := ⟨⟨360585945925675510, 360585992872737563⟩, ⟨(-303164481598298612), (-300478771265508594)⟩, true⟩

def words00 : List Nat := [360582445231314071, 360582445322436194, 360582445513559790, 360582445704911937, 360582445777275894, 360582445778492952, 360582445768886776, 360582445755933812, 360582445742607203, 360582445768214355]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 84700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 84700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587050007553199, 360587096966191606⟩, ⟨(-396708737900436820), (-394022046875369940)⟩, true⟩

def words01 : List Nat := [360582445769308601, 360582445683374573, 360582445649294846, 360582445810399292, 360582445936114581, 360582446062025478, 360582446118003943, 360582446119220726, 360582446090784683, 360582446147069130]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 84710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 84700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583400389779811, 360583447359897685⟩, ⟨(-87570861504428156), (-84883197883806264)⟩, true⟩

def words02 : List Nat := [360582446148077122, 360582446120587705, 360582446071919921, 360582445944830135, 360582445817545757, 360582445654165018, 360582445584298179, 360582445607872146, 360582445608956460, 360582445563649750]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 84720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 84700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360610174199018176, 360610221180618201⟩, ⟨(-2356283544307280736), (-2353594907747610004)⟩, true⟩

def words03 : List Nat := [360582445715634883, 360582445867975814, 360582446041662073, 360582446175371357, 360582446176523982, 360582446177431669, 360582446316955663, 360582446542044359, 360582446870791167, 360582447199809058]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 84730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 84700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594403410402734, 360594450403610443⟩, ⟨(-1019815167075049121), (-1017125546823933347)⟩, true⟩

def words04 : List Nat := [360582447446759640, 360582447697666713, 360582448056441263, 360582448415586585, 360582448691745148, 360582448828986036, 360582448860820988, 360582448892782157, 360582448920841572, 360582449063840719]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 84740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 84700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk847A
