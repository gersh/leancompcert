import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk833

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

def state06 : KState := ⟨⟨360591607031888884, 360591652437981911⟩, ⟨(-770436739741987980), (-767880527610154258)⟩, true⟩

def words05 : List Nat := [360582441367039566, 360582441355834364, 360582441344278944, 360582441336003941, 360582441228600345, 360582440998878448, 360582440768906289, 360582440706657686, 360582440818130555, 360582440929871282]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360558411688876942, 360558457106372220⟩, ⟨1996812713156275375, 1999369875836495735⟩, true⟩

def words06 : List Nat := [360582440948939816, 360582440950135766, 360582440825536149, 360582440697441171, 360582440569032166, 360582440404639913, 360582440136596836, 360582439776056645, 360582439415304204, 360582438992852207]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360525034885026589, 360525080313778320⟩, ⟨4779673059472332661, 4782231160659928643⟩, true⟩

def words07 : List Nat := [360582438706166446, 360582438539170396, 360582438372045316, 360582438132944060, 360582437750116579, 360582437269413913, 360582436788375212, 360582436270467325, 360582435655731507, 360582434969099260]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360559755450763729, 360559800890795791⟩, ⟨1884502727537515759, 1887061769335250673⟩, true⟩

def words08 : List Nat := [360582434282203820, 360582433716381786, 360582433240488369, 360582432908578951, 360582432576577078, 360582432110935922, 360582431532344019, 360582431055149924, 360582430577615934, 360582430244067590]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360570280818017243, 360570326269459759⟩, ⟨1006665590922071377, 1009225584291261715⟩, true⟩

def words09 : List Nat := [360582429973797167, 360582429568634944, 360582429163253256, 360582428867281507, 360582428659662232, 360582428372884691, 360582428085983528, 360582427727187114, 360582427439381816, 360582427295650302]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk833
