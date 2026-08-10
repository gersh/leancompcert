import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk278A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360646605553628314, 360646610171561354⟩, ⟨(-1782517685684672078), (-1782430853763331572)⟩, true⟩

def state01 : KState := ⟨⟨360617579757065150, 360617584378489090⟩, ⟨(-975774395549044932), (-975687466563662382)⟩, true⟩

def words00 : List Nat := [360582497916860921, 360582498284173781, 360582499941188175, 360582501598197356, 360582502702123336, 360582502702489709, 360582502517133121, 360582501357292729, 360582500326770637, 360582501588709375]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 27800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 27800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360548815341428667, 360548819966308888⟩, ⟨936810256511649808, 936897281633602214⟩, true⟩

def words01 : List Nat := [360582502371417536, 360582503154135105, 360582503197454382, 360582503197820963, 360582501952447824, 360582500378677781, 360582498804912892, 360582498520107539, 360582498289434541, 360582497079236049]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 27810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 27800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360633246328807936, 360633250957146993⟩, ⟨(-1412498966876911083), (-1412411845513213215)⟩, true⟩

def words02 : List Nat := [360582495869040204, 360582495712080014, 360582497247924417, 360582498783728803, 360582499105449699, 360582499105816366, 360582498461943759, 360582498784247700, 360582499542983989, 360582501366923386]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 27820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 27800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573147735156353, 360573152366989040⟩, ⟨260470588831596229, 260557807440692817⟩, true⟩

def words03 : List Nat := [360582502542513972, 360582503718066520, 360582505270290273, 360582507473561973, 360582509069014254, 360582510664411064, 360582511607830208, 360582511819102617, 360582511819404603, 360582511483635617]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 27830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 27800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575354690471492, 360575359325759287⟩, ⟨198811920148761421, 198899234964954695⟩, true⟩

def words04 : List Nat := [360582511147771269, 360582511000092031, 360582509566552998, 360582507485846040, 360582505405228785, 360582502996880262, 360582501743225056, 360582501759590164, 360582501759917091, 360582501129528227]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 27840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 27800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk278A
