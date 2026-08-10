import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk792A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360595973627472661, 360596014451910444⟩, ⟨(-1096371279028645886), (-1094187551049628058)⟩, true⟩

def state01 : KState := ⟨⟨360592311732966303, 360592352568046868⟩, ⟨(-806351373931810755), (-804166802989971887)⟩, true⟩

def words00 : List Nat := [360582199461465912, 360582199650270642, 360582199727987818, 360582199805823639, 360582199806788197, 360582199809266926, 360582199981575718, 360582200154096882, 360582200227486325, 360582200356826331]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 79200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 79200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590092329189288, 360590133174969550⟩, ⟨(-630581612063919961), (-628396193547474793)⟩, true⟩

def words01 : List Nat := [360582200444919628, 360582200533358795, 360582200752040993, 360582200811881231, 360582200812925269, 360582200736423224, 360582200675155486, 360582200780463268, 360582200881525615, 360582200982829241]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 79210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 79200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360611745708632954, 360611786565190639⟩, ⟨(-2346154133688386192), (-2343967861330816456)⟩, true⟩

def words02 : List Nat := [360582201004321218, 360582201079858064, 360582201281158819, 360582201482786744, 360582201642272830, 360582201806332475, 360582201889971011, 360582201973722315, 360582202216284061, 360582202590971826]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 79220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 79200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360571910686579474, 360571951553816459⟩, ⟨810259283534961763, 812446402065726583⟩, true⟩

def words03 : List Nat := [360582203124297549, 360582203657826672, 360582204042893434, 360582204305996178, 360582204438854147, 360582204572015592, 360582204697566197, 360582204698698458, 360582204665384860, 360582204537184275]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 79230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 79200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581712853083588, 360581753731004347⟩, ⟨33573332590967400, 35761297756482672⟩, true⟩

def words04 : List Nat := [360582204438317149, 360582204560324272, 360582204811388251, 360582205062670389, 360582205174681375, 360582205175813740, 360582205128764389, 360582205078151743, 360582205027204478, 360582204977663735]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 79240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 79200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk792A
