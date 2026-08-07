import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk750

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586980938397462, 360587017391095317⟩, ⟨(-355415863147775415), (-353569285507084485)⟩, true⟩

def state01 : KState := ⟨⟨360581520750290075, 360581557213041207⟩, ⟨54086055292268004, 55933386979397224⟩, true⟩

def words00 : List Nat := [360582303404058488, 360582303433905982, 360582303434858865, 360582303352063979, 360582303269110017, 360582303064925429, 360582302974220661, 360582303000249676, 360582303001207743, 360582302892110390]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 75000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 75000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360603107170728556, 360603143643570573⟩, ⟨(-1565198223672201486), (-1563350135019074696)⟩, true⟩

def words01 : List Nat := [360582303050575032, 360582303219312813, 360582303565187417, 360582303733698539, 360582303752254797, 360582303770884216, 360582303966772538, 360582304252422795, 360582304531086146, 360582304809977059]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 75010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 75000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599720098680923, 360599756581688224⟩, ⟨(-1311269827009795059), (-1309420975706848533)⟩, true⟩

def words02 : List Nat := [360582304963767309, 360582304964835358, 360582304941012567, 360582304907103983, 360582304872903416, 360582304793903266, 360582304778360210, 360582304665157877, 360582304614912563, 360582304848728423]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 75020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 75000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360568861587455746, 360568898080540049⟩, ⟨1004163002574809808, 1006012610004771476⟩, true⟩

def words03 : List Nat := [360582305036430502, 360582305224324533, 360582305272854844, 360582305273923114, 360582305144890097, 360582304937039662, 360582304728875165, 360582304698321333, 360582304609485854, 360582304431952693]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 75030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 75000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582957381098854, 360582993884266197⟩, ⟨(-53563312681961663), (-51712948571620401)⟩, true⟩

def words04 : List Nat := [360582304254162863, 360582304391016549, 360582304661990847, 360582304933162543, 360582305053119339, 360582305054187827, 360582305040760838, 360582304981890972, 360582304922714131, 360582304846830699]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 75040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 75000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360568280318986290, 360568316832335426⟩, ⟨1048024485631858890, 1049875613935242440⟩, true⟩

def words05 : List Nat := [360582304847792565, 360582304756405609, 360582304664821516, 360582304671225278, 360582304672122165, 360582304638548243, 360582304604858950, 360582304475836051, 360582304169250358, 360582303984133125]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566034042953469, 360566070566378423⟩, ⟨1216599099647575527, 1218450984293373061⟩, true⟩

def words06 : List Nat := [360582303798668576, 360582303609243807, 360582303367173724, 360582303024343373, 360582302681340802, 360582302293729952, 360582301995116601, 360582301843284501, 360582301691332169, 360582301430695639]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588329114407911, 360588365647923349⟩, ⟨(-457272691357783470), (-455420049171272836)⟩, true⟩

def words07 : List Nat := [360582301215353436, 360582301105799174, 360582300995929894, 360582300988709898, 360582300804164969, 360582300442024586, 360582300079689282, 360582299864418794, 360582299849678174, 360582299931574722]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360589914229770440, 360589950773481667⟩, ⟨(-576304497372973453), (-574451089636738393)⟩, true⟩

def words08 : List Nat := [360582299932528137, 360582299923877175, 360582300120349621, 360582300317130452, 360582300468785631, 360582300594958850, 360582300623551048, 360582300652256330, 360582300653138238, 360582300707699660]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554485628652323, 360554522182425929⟩, ⟨2084278934842709985, 2086133098214727857⟩, true⟩

def words09 : List Nat := [360582300935488235, 360582301163475251, 360582301302589371, 360582301303658521, 360582301265520136, 360582301135375115, 360582301004894101, 360582300901971658, 360582300621752624, 360582300252974727]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk750
