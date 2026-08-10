import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk357A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598484122942364, 360598491900799200⟩, ⟨(-584972655208232733), (-584784939652633217)⟩, true⟩

def state01 : KState := ⟨⟨360569206162925080, 360569213945289651⟩, ⟨460333874482001025, 460521750987258543⟩, true⟩

def words00 : List Nat := [360582112628490024, 360582112646809666, 360582112647240606, 360582112273353938, 360582111899410279, 360582111140866480, 360582110995774486, 360582110829441181, 360582110663064817, 360582110101856083]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 35700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 35700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360578545363829511, 360578553150719820⟩, ⟨126732875445643587, 126920913587659001⟩, true⟩

def words01 : List Nat := [360582109741120224, 360582109257241641, 360582108838869201, 360582108929448187, 360582108929890200, 360582108354678037, 360582107779410028, 360582106927545998, 360582106466765015, 360582106367785544]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 35710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 35700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360562811719021373, 360562819510489197⟩, ⟨688546186473030686, 688734388146170206⟩, true⟩

def words02 : List Nat := [360582106268753357, 360582105567310698, 360582104370704293, 360582103773047421, 360582103175295183, 360582102362739676, 360582100770265673, 360582098783492844, 360582096796727610, 360582095591881478]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 35720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 35700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360511364339409491, 360511372135391691⟩, ⟨2527221344449105156, 2527409707443935524⟩, true⟩

def words03 : List Nat := [360582095294944474, 360582095537563469, 360582095537990977, 360582095315556739, 360582094836746696, 360582093818557206, 360582092800286150, 360582092013315382, 360582090669477681, 360582088691279882]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 35730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 35700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580535004537134, 360580542805056677⟩, ⟨54754962081227972, 54943487262075004⟩, true⟩

def words04 : List Nat := [360582086713084387, 360582085297792752, 360582084576321653, 360582084320779727, 360582084065214577, 360582083145920440, 360582081700360174, 360582081035936370, 360582080371410636, 360582079685819253]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 35740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 35700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk357A
