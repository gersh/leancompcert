import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk909A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk909B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk909A

def state06 : KState := ⟨⟨360594899755079875, 360594954184452811⟩, ⟨(-1182614283377451543), (-1179271065520920831)⟩, true⟩

def words05 : List Nat := [360581988436682005, 360581988495136854, 360581988606397069, 360581988791012855, 360581988944927772, 360581989099053714, 360581989192459317, 360581989317874230, 360581989461477151, 360581989605506660]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 90950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 90900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583667805423131, 360583722247161838⟩, ⟨(-160958911084672911), (-157614568374366235)⟩, true⟩

def words06 : List Nat := [360581989785587210, 360581989845250875, 360581989846433640, 360581989845929598, 360581989845232082, 360581989745028217, 360581989705085680, 360581989706184530, 360581989707139858, 360581989666796949]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 90960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 90900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602370714955015, 360602425169109973⟩, ⟨(-1862433366089458759), (-1859087893812549821)⟩, true⟩

def words07 : List Nat := [360581989807575639, 360581989948779512, 360581990154957903, 360581990326363411, 360581990394092863, 360581990461921571, 360581990650152383, 360581990913776741, 360581991139459593, 360581991365416757]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 90970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 90900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601885062822179, 360601939529505010⟩, ⟨(-1818382757573419933), (-1815036145450755301)⟩, true⟩

def words08 : List Nat := [360581991498174734, 360581991510443136, 360581991593454909, 360581991676854372, 360581991707515802, 360581991779317753, 360581991780494228, 360581991775240879, 360581991883793461, 360581992104534950]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 90980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 90900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360581373596384025, 360581428075461435⟩, ⟨48074247661537462, 51421987628770526⟩, true⟩

def words09 : List Nat := [360581992377889725, 360581992651497586, 360581992831797262, 360581992891626566, 360581992920958747, 360581992950638964, 360581993100539117, 360581993155883577, 360581993157065563, 360581993152248565]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 90900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 90900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk909B
