import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk974A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360605451591544088, 360605514333522656⟩, ⟨(-2256604712313572654), (-2252478287289413532)⟩, true⟩

def state01 : KState := ⟨⟨360587540808558415, 360587603563994110⟩, ⟨(-512055574183992827), (-507927838370329261)⟩, true⟩

def words00 : List Nat := [360582388696329423, 360582388818997021, 360582389028754114, 360582389238922326, 360582389342494691, 360582389362450467, 360582389363722256, 360582389321945149, 360582389279903598, 360582389288005050]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 97400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 97400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569503486751565, 360569566255521872⟩, ⟨1245090302741370105, 1249219337545619135⟩, true⟩

def words01 : List Nat := [360582389399510252, 360582389511308642, 360582389559654983, 360582389561069619, 360582389537512002, 360582389487660412, 360582389460848352, 360582389462262906, 360582389413169779, 360582389283006430]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 97410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 97400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593162583868158, 360593225365986599⟩, ⟨(-1059882088821940502), (-1055751753575883340)⟩, true⟩

def words02 : List Nat := [360582389152525383, 360582389083281840, 360582389182467727, 360582389285558839, 360582389298234501, 360582389313347597, 360582389314501832, 360582389295796609, 360582389361714325, 360582389474395875]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 97420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 97400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590024394236664, 360590087189847432⟩, ⟨(-754166873675624733), (-750035223805506575)⟩, true⟩

def words03 : List Nat := [360582389527224010, 360582389580208197, 360582389607719828, 360582389689075926, 360582389712858123, 360582389736865092, 360582389738125317, 360582389709306715, 360582389782376695, 360582389863015755]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 97430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 97400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585334285980305, 360585397094905068⟩, ⟨(-297121080498563008), (-292988133244714850)⟩, true⟩

def words04 : List Nat := [360582390048436583, 360582390155459237, 360582390208548174, 360582390261781204, 360582390288094147, 360582390374190431, 360582390457496739, 360582390541059391, 360582390545124190, 360582390577442500]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 97440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 97400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk974A
