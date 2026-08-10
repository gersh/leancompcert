import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk761A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586414806885463, 360586452379799792⟩, ⟨(-326613446060601331), (-324682234546148405)⟩, true⟩

def state01 : KState := ⟨⟨360567725269850297, 360567762853093810⟩, ⟨1095736600645958464, 1097668598261304674⟩, true⟩

def words00 : List Nat := [360582185916008122, 360582185886769883, 360582185896557918, 360582185988457858, 360582186008284331, 360582186009368859, 360582185856926315, 360582185596399662, 360582185335680774, 360582184986824743]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360549512279061983, 360549549872531612⟩, ⟨2481993425519888739, 2483926201496762231⟩, true⟩

def words01 : List Nat := [360582184798228946, 360582184575176699, 360582184352021781, 360582184042995930, 360582183659998227, 360582183181844218, 360582182703384573, 360582182357204891, 360582182015826221, 360582181588263309]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594265407088930, 360594303010792206⟩, ⟨(-924857836665468040), (-922924281653000698)⟩, true⟩

def words02 : List Nat := [360582181160458231, 360582180872299477, 360582180670136287, 360582180640538916, 360582180610877640, 360582180414933126, 360582180161937542, 360582180052967634, 360582180005836595, 360582180166199951]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360568810884964916, 360568848499018252⟩, ⟨1013168363441609295, 1015102706454483675⟩, true⟩

def words03 : List Nat := [360582180195504219, 360582180224929241, 360582180330105600, 360582180522019861, 360582180670141445, 360582180818436890, 360582180858983660, 360582180860068647, 360582180728377937, 360582180554527242]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576981213096234, 360577018837367082⟩, ⟨391001349138201127, 392936470163659885⟩, true⟩

def words04 : List Nat := [360582180380311773, 360582180257853619, 360582180110287824, 360582179842563125, 360582179574668693, 360582179229919290, 360582179032276800, 360582179007097837, 360582178981810373, 360582178869805213]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk761A
