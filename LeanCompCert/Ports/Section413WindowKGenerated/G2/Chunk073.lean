import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk073

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360384463026164574, 360384463306838995⟩, ⟨1470978289582914671, 1470979679035545013⟩, true⟩

def state01 : KState := ⟨⟨360736771090817151, 360736771372298907⟩, ⟨(-1103576393486911756), (-1103574998136808354)⟩, true⟩

def words00 : List Nat := [360585939773014717, 360585909884242807, 360585889579751153, 360585880699736078, 360585871822145010, 360585847047505747, 360585817590447204, 360585806709702708, 360585803520208002, 360585824169708727]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 7300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 7300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360537220457001263, 360537220739297166⟩, ⟨356519902530175853, 356521303835718911⟩, true⟩

def words01 : List Nat := [360585835462751829, 360585846752715780, 360585868696771542, 360585903236168242, 360585920041839798, 360585936842930001, 360585943894298624, 360585943894384260, 360585932489962966, 360585925835449587]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 7310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 7300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360661234319477040, 360661234602580800⟩, ⟨(-551402590711632813), (-551401183488486829)⟩, true⟩

def words02 : List Nat := [360585931022469982, 360585943868504325, 360585947411994436, 360585950954526409, 360585950954598285, 360585964059970810, 360585984090850869, 360586004116280848, 360586009338714698, 360586019600058841]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 7320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 7300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360839300174490097, 360839300458403589⟩, ⟨(-1857114283606187993), (-1857112870443669337)⟩, true⟩

def words03 : List Nat := [360586048298706382, 360586076989551933, 360586124107684523, 360586164516278656, 360586188630776466, 360586212738708358, 360586228313413799, 360586253330510659, 360586287805665793, 360586322271447634]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 7330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 7300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604337109239352, 360604337393972610⟩, ⟨(-132881664109422756), (-132880244925841214)⟩, true⟩

def words04 : List Nat := [360586347482134228, 360586354376817820, 360586360609929412, 360586366841368651, 360586366841440993, 360586362741856376, 360586340344076135, 360586306917089330, 360586273499182709, 360586260908470524]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 7340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 7300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360329343776780366, 360329344062323634⟩, ⟨1890474971385562202, 1890476396526899876⟩, true⟩

def words05 : List Nat := [360586281720989008, 360586302527862857, 360586311146485084, 360586311146571131, 360586301493269620, 360586286907388610, 360586272325449066, 360586257113779247, 360586237172239466, 360586202268373485]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 7350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 7300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360651411964703170, 360651412251059924⟩, ⟨(-482172070948344229), (-482170639815686667)⟩, true⟩

def words06 : List Nat := [360586167373971812, 360586137981374928, 360586118078225153, 360586107890119415, 360586097704772188, 360586071888417844, 360586038410604438, 360586015792151112, 360585993179811695, 360585997702177047]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 7360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 7300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360717192883452660, 360717193170633123⟩, ⟨(-967918622988503959), (-967917185781236467)⟩, true⟩

def words07 : List Nat := [360585997702256372, 360585991653885590, 360585990196851546, 360586004146535683, 360586010506741129, 360586016865236153, 360586016865313120, 360586021306284380, 360586039080319749, 360586056849568060]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 7370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 7300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360511900853291188, 360511901141285244⟩, ⟨547425830632476729, 547427273848267495⟩, true⟩

def words08 : List Nat := [360586073941075316, 360586073941161723, 360586072897600529, 360586059765794122, 360586046637530890, 360586020559846086, 360586003803587297, 360585998342023469, 360585992881929241, 360585977903646309]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 7380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 7300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360526408948708593, 360526409237521860⟩, ⟨440260647158753895, 440262096432577743⟩, true⟩

def words09 : List Nat := [360585967881153689, 360585965185551363, 360585977920033372, 360585977920119946, 360585975279513514, 360585954680660613, 360585934087361121, 360585918167579586, 360585912156263361, 360585904115418155]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 7390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 7300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 7300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk073
