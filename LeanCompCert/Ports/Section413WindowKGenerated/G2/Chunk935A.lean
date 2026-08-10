import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk935A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603365551809306, 360603423187173001⟩, ⟨(-2001316338017031007), (-1997677411673735141)⟩, true⟩

def state01 : KState := ⟨⟨360601456532704316, 360601514180952211⟩, ⟨(-1822892790838260823), (-1819252659756582753)⟩, true⟩

def words00 : List Nat := [360582058053226111, 360582058110627759, 360582058282110683, 360582058453987537, 360582058596680781, 360582058742490461, 360582058821120249, 360582058899896052, 360582059012462175, 360582059222072972]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577952698606395, 360578010359614353⟩, ⟨375056840888471700, 378698165227684800⟩, true⟩

def words01 : List Nat := [360582059448467576, 360582059675109368, 360582059807302700, 360582059825556416, 360582059826689454, 360582059794510480, 360582059766971166, 360582059781849778, 360582059783067125, 360582059741192922]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598272992299071, 360598330666082888⟩, ⟨(-1525377810856469107), (-1521735291657846603)⟩, true⟩

def words02 : List Nat := [360582059723706534, 360582059841284790, 360582060072732019, 360582060304433949, 360582060433998227, 360582060478931938, 360582060494821164, 360582060511103215, 360582060641248144, 360582060816603488]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360588847088245483, 360588904774920415⟩, ⟨(-643723347142910195), (-640079622175222397)⟩, true⟩

def words03 : List Nat := [360582060934309502, 360582061052161038, 360582061185237068, 360582061422052690, 360582061594936150, 360582061768032390, 360582061868546736, 360582061869900750, 360582061929435362, 360582062004133539]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576023302015032, 360576081001457521⟩, ⟨555802069081893932, 559446988391267498⟩, true⟩

def words04 : List Nat := [360582062035013249, 360582062036367289, 360582061953334887, 360582061813039368, 360582061672516988, 360582061485679696, 360582061356200897, 360582061321236395, 360582061286094626, 360582061193743906]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk935A
