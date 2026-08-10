import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk714A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk714B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk714A

def state06 : KState := ⟨⟨362499527836290536, 362499603743178165⟩, ⟨(-1030106979784413435), (-1026443687617225645)⟩, true⟩

def words05 : List Nat := [371285237823086102, 371285237993938101, 371285238359491383, 371285238628092948, 371285238947167561, 371285239267272609, 371285239586757587, 371285239645954716, 371285239848628944, 371285240052667016]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480937944973343, 362481013873698065⟩, ⟨298403279157980556, 302068131918320174⟩, true⟩

def words06 : List Nat := [371285240335356173, 371285240357947208, 371285240359811725, 371285240335583470, 371285240342731498, 371285240345432256, 371285240319890524, 371285240347914833, 371285240373593042, 371285240376173486]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362509122333120617, 362509198284011674⟩, ⟨(-1716063063032973518), (-1712396625931687864)⟩, true⟩

def words07 : List Nat := [371285240455139865, 371285240594541430, 371285240928204956, 371285241075660357, 371285241188908222, 371285241302891589, 371285241497833205, 371285241640198442, 371285241977012384, 371285242314929937]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490308095386236, 362490384068387663⟩, ⟨(-371134609870839278), (-367466592208329052)⟩, true⟩

def words08 : List Nat := [371285242652250072, 371285242749559186, 371285243041600573, 371285243334933712, 371285243627125306, 371285243699488045, 371285243764611368, 371285243830569003, 371285243953797407, 371285244028491616]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477349104156191, 362477425099236969⟩, ⟨555390062103800167, 559059658329574019⟩, true⟩

def words09 : List Nat := [371285244180761370, 371285244333973008, 371285244486742020, 371285244489193074, 371285244381205532, 371285244328390736, 371285244327442422, 371285244329936339, 371285244222030211, 371285244115437383]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk714B
