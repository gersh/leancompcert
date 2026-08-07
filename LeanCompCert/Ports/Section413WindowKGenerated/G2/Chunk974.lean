import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk974

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

def state06 : KState := ⟨⟨360609366108742629, 360609428931015634⟩, ⟨(-2639199113359549862), (-2635064865253456768)⟩, true⟩

def words05 : List Nat := [360582390602405858, 360582390627794877, 360582390758012518, 360582390890807908, 360582390932480164, 360582390974261457, 360582391078655348, 360582391252397306, 360582391530964374, 360582391809856879]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594098680651141, 360594161516428499⟩, ⟨(-1151249470606795523), (-1147113906304831413)⟩, true⟩

def words06 : List Nat := [360582391995620810, 360582392076585457, 360582392262515854, 360582392448859435, 360582392592356753, 360582392631180542, 360582392632441492, 360582392610854587, 360582392622762434, 360582392745139554]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588981869222136, 360589044718318940⟩, ⟨(-652489788551261822), (-648352925935896604)⟩, true⟩

def words07 : List Nat := [360582392883191642, 360582393021504429, 360582393106862691, 360582393212125831, 360582393242332220, 360582393272891288, 360582393387062784, 360582393509414344, 360582393578918443, 360582393648613707]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597105009330301, 360597167871806276⟩, ⟨(-1444303165608635010), (-1440164998726159748)⟩, true⟩

def words08 : List Nat := [360582393785317556, 360582394020264402, 360582394330372558, 360582394640745636, 360582394849591797, 360582394980959441, 360582395143074965, 360582395305612200, 360582395432155110, 360582395585146727]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360591146673130678, 360591209549087800⟩, ⟨(-863429172898046252), (-859289691674600486)⟩, true⟩

def words09 : List Nat := [360582395685164875, 360582395785335598, 360582395901427712, 360582396070237305, 360582396150903022, 360582396231818168, 360582396241656275, 360582396243073863, 360582396319856137, 360582396411872032]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk974
