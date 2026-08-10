import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk833A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360591037352574549, 360591082690787973⟩, ⟨(-721981084211928675), (-719430528483558305)⟩, true⟩

def state01 : KState := ⟨⟨360576874435306139, 360576919784893339⟩, ⟨457738169034549648, 460289672255894836⟩, true⟩

def words00 : List Nat := [360582446205967784, 360582446207162851, 360582446095778219, 360582446006964605, 360582445917817506, 360582445792677970, 360582445600451459, 360582445297839739, 360582444995006114, 360582444807966871]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360560799307965019, 360560844668805456⟩, ⟨1797148547396258139, 1799700988181808561⟩, true⟩

def words01 : List Nat := [360582444820283960, 360582444899146779, 360582444905614512, 360582444990187960, 360582445005798359, 360582445021723605, 360582445022698024, 360582444980606268, 360582444794648128, 360582444536642492]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575939872236873, 360575985244379473⟩, ⟨535529061938785481, 538082444475616941⟩, true⟩

def words02 : List Nat := [360582444278388882, 360582444016646412, 360582443827767506, 360582443743989086, 360582443660128003, 360582443428079572, 360582443094665613, 360582442871315439, 360582442647597119, 360582442492003086]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574427185083970, 360574472568613759⟩, ⟨661590137343615145, 664144468830142121⟩, true⟩

def words03 : List Nat := [360582442415589349, 360582442258395269, 360582442100975834, 360582442136197278, 360582442137215201, 360582442114745180, 360582442092137207, 360582441997495531, 360582441758958036, 360582441664712033]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577333293150794, 360577378687952880⟩, ⟨419424012790872480, 421979283766839518⟩, true⟩

def words04 : List Nat := [360582441618312217, 360582441671117946, 360582441672188225, 360582441633944428, 360582441595506646, 360582441500670800, 360582441506678569, 360582441521503731, 360582441522599203, 360582441426810311]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk833A
