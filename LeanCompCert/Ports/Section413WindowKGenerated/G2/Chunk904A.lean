import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk904A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360563814648998507, 360563868384402325⟩, ⟨1635542123048762450, 1638822411600590364⟩, true⟩

def state01 : KState := ⟨⟨360594787779979351, 360594841527699053⟩, ⟨(-1164533191447275999), (-1161251789480168291)⟩, true⟩

def words00 : List Nat := [360581996751422215, 360581996687113373, 360581996822938495, 360581996959010930, 360581996970664632, 360581996971973305, 360581997035628742, 360581997129488154, 360581997241540045, 360581997384956686]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580433418028533, 360580487178191224⟩, ⟨133343599242051032, 136626126242308392⟩, true⟩

def words01 : List Nat := [360581997466807113, 360581997548820923, 360581997688401235, 360581997889734200, 360581998020697567, 360581998151865772, 360581998221532206, 360581998222837769, 360581998210061543, 360581998194849511]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580552113160263, 360580605885610796⟩, ⟨122586114342945405, 125869752470931519⟩, true⟩

def words02 : List Nat := [360581998216263461, 360581998217569910, 360581998190187011, 360581998079644397, 360581997968892337, 360581997827180392, 360581997804961356, 360581997832124458, 360581997833287824, 360581997788214699]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591943115341028, 360591996900127623⟩, ⟨(-907645291500187151), (-904360537760064613)⟩, true⟩

def words03 : List Nat := [360581997777096321, 360581997781759650, 360581997783207178, 360581997784512709, 360581997694554151, 360581997500702182, 360581997306602358, 360581997235039158, 360581997335082009, 360581997447028254]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591899565128038, 360591953362353395⟩, ⟨(-903782626545923707), (-900496747784782139)⟩, true⟩

def words04 : List Nat := [360581997480979025, 360581997496261888, 360581997607156622, 360581997718432509, 360581997798685355, 360581997806900257, 360581997808084117, 360581997713725117, 360581997620130191, 360581997731704925]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk904A
