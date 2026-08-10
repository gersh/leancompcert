import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk692A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588839256983677, 360588870092031935⟩, ⟨(-424886686982030133), (-423445376430976061)⟩, true⟩

def state01 : KState := ⟨⟨360574170250856976, 360574201095247217⟩, ⟨590245312732964850, 591687269795172586⟩, true⟩

def words00 : List Nat := [360582751028506506, 360582750956555339, 360582751032533115, 360582751175373742, 360582751265591783, 360582751266570902, 360582751148290306, 360582750851475415, 360582750554495138, 360582750253891852]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 69200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 69200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360546871508121873, 360546902361732357⟩, ⟨2479785402175361227, 2481227997417954961⟩, true⟩

def words01 : List Nat := [360582750157013391, 360582750183855891, 360582750184728560, 360582750107460829, 360582749821519265, 360582749459323492, 360582749096833926, 360582748826751582, 360582748414510457, 360582747897667318]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 69210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 69200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360563947239127743, 360563978102001330⟩, ⟨1297662568026903431, 1299105804505537471⟩, true⟩

def words02 : List Nat := [360582747380617362, 360582747072085098, 360582746877388024, 360582746521401731, 360582746165352601, 360582745627701107, 360582744881424677, 360582744256172972, 360582743630641110, 360582743172122745]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 69220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 69200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573256652220974, 360573287524419153⟩, ⟨653109798640191663, 654553680706445527⟩, true⟩

def words03 : List Nat := [360582742901945852, 360582742513394731, 360582742124667389, 360582741944383147, 360582741921007118, 360582741806415862, 360582741691742922, 360582741407520527, 360582741063657701, 360582740928242181]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 69230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 69200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567308597308157, 360567339478727118⟩, ⟨1064936663626685021, 1066381184187150063⟩, true⟩

def words04 : List Nat := [360582740792507580, 360582740728225137, 360582740510688572, 360582740189260824, 360582739867671252, 360582739409704049, 360582739055884146, 360582738910326500, 360582738764666765, 360582738484996969]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 69240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 69200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk692A
