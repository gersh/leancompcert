import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk673A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360574664455467994, 360574693556064996⟩, ⟨554054808454078736, 555377734562766312⟩, true⟩

def state01 : KState := ⟨⟨360573503092462396, 360573532202025594⟩, ⟨632197562064539795, 633521091642456427⟩, true⟩

def words00 : List Nat := [360582945703678686, 360582945570327135, 360582945547208617, 360582945505928256, 360582945464590192, 360582945215351423, 360582944806018788, 360582944617342758, 360582944428399282, 360582944192690317]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 67300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 67300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360559362215095278, 360559391333732986⟩, ⟨1584157373910161804, 1585481514336419336⟩, true⟩

def words01 : List Nat := [360582944053717414, 360582943801376270, 360582943548844232, 360582943519895706, 360582943520691122, 360582943520702871, 360582943520612828, 360582943385892085, 360582943101287318, 360582942752543688]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 67310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 67300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360559274802000802, 360559303929580562⟩, ⟨1590020368994271029, 1591345111445375393⟩, true⟩

def words02 : List Nat := [360582942403475692, 360582942159212828, 360582941789491240, 360582941309655387, 360582940829679717, 360582940293039476, 360582939933213673, 360582939638612878, 360582939343925095, 360582938937919273]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 67320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 67300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565761147272270, 360565790283841632⟩, ⟨1153161591889750727, 1154486939653289633⟩, true⟩

def words03 : List Nat := [360582938587665924, 360582938271613065, 360582937955303385, 360582937634265357, 360582937148530245, 360582936466105159, 360582935783518398, 360582935159605708, 360582934685627898, 360582934432039632]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 67330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 67300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572631948132549, 360572661093745239⟩, ⟨690351126230256459, 691677083016645393⟩, true⟩

def words04 : List Nat := [360582934178299556, 360582933814520468, 360582933417596617, 360582933241078319, 360582933064311764, 360582932832340987, 360582932441123724, 360582931881929728, 360582931322570240, 360582930983619280]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 67340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 67300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk673A
