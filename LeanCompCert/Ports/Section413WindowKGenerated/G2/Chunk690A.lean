import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk690A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569233788524218, 360569264438604422⟩, ⟨931066888273182597, 932495417532300869⟩, true⟩

def state01 : KState := ⟨⟨360570370088897212, 360570400748170143⟩, ⟨852603785227878696, 854032948830345574⟩, true⟩

def words00 : List Nat := [360582778683605613, 360582778684581564, 360582778489423055, 360582778089913173, 360582777690251715, 360582777189708142, 360582776853795327, 360582776685427925, 360582776516957034, 360582776243733545]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 69000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 69000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595872640411026, 360595903308913192⟩, ⟨(-907488519156193779), (-906058718599590395)⟩, true⟩

def words01 : List Nat := [360582776095396977, 360582776126683524, 360582776153626045, 360582776154608766, 360582776151118895, 360582775965247522, 360582775779198489, 360582775655445275, 360582775827171448, 360582776018398717]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 69010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 69000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360572732720331817, 360572763398137522⟩, ⟨689598910606718000, 691029353338429424⟩, true⟩

def words02 : List Nat := [360582776104052637, 360582776105028931, 360582775980946249, 360582775956196092, 360582775931194583, 360582775763162714, 360582775385412035, 360582774841763980, 360582774297944841, 360582773963881959]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 69020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 69000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360554320670294545, 360554351357289521⟩, ⟨1960791907635151859, 1962222984749678997⟩, true⟩

def words03 : List Nat := [360582773884039114, 360582773949396775, 360582773950266918, 360582773910843046, 360582773877748129, 360582773792358095, 360582773706679743, 360582773611153803, 360582773305970143, 360582772895307333]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 69030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 69000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360566524706081382, 360566555402311634⟩, ⟨1118132439559698712, 1119564154322344250⟩, true⟩

def words04 : List Nat := [360582772484449263, 360582772062855613, 360582771778106373, 360582771496772682, 360582771215371008, 360582770755187176, 360582770318432040, 360582769914603086, 360582769510471173, 360582769220621878]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 69040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 69000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk690A
