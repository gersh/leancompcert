import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk368A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk368B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk368A

def state06 : KState := ⟨⟨360614899488326045, 360614907801583109⟩, ⟨(-1225725522332024508), (-1225518380692798758)⟩, true⟩

def words05 : List Nat := [360581655360420218, 360581656053147707, 360581657294995206, 360581657801963038, 360581657802435161, 360581657636203508, 360581658038292822, 360581658977293824, 360581659879725792, 360581660782221378]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 36850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 36800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576747887606574, 360576756205593543⟩, ⟨180674961818357582, 180882277826054470⟩, true⟩

def words06 : List Nat := [360581661134435336, 360581661514007272, 360581662460235237, 360581663406562220, 360581664019309246, 360581664019805603, 360581663898167042, 360581663405898153, 360581662913566200, 360581662152917277]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 36860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 36800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360538134249810177, 360538142572469333⟩, ⟨1604695547552857718, 1604903035847644316⟩, true⟩

def words07 : List Nat := [360581662621873097, 360581663223951693, 360581663299283354, 360581663299779854, 360581662864600375, 360581662126124822, 360581661387534607, 360581661383541689, 360581660645543415, 360581659466066070]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 36870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 36800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563357528444566, 360563365855797285⟩, ⟨674165040870613151, 674372702286779941⟩, true⟩

def words08 : List Nat := [360581658286542270, 360581657324994856, 360581656729037473, 360581655755522887, 360581654782022254, 360581653187903546, 360581650860062602, 360581649266645906, 360581647673169844, 360581646492888280]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 36880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 36800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575865782275240, 360575874114361948⟩, ⟨212651325033736910, 212859161108764238⟩, true⟩

def words09 : List Nat := [360581645997803703, 360581645137387199, 360581644276921609, 360581644281857627, 360581644282809554, 360581644283842476, 360581644284292710, 360581643700722856, 360581642811074339, 360581642655313406]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 36890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 36800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 36800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk368B
