import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk421A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk421B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk421A

def state06 : KState := ⟨⟨360545744527821834, 360545755523424909⟩, ⟨1550427089964042987, 1550740382739201343⟩, true⟩

def words05 : List Nat := [360582541511006432, 360582541342057015, 360582541173049197, 360582540721898665, 360582540284801854, 360582539703703205, 360582539122458348, 360582539103235462, 360582538662437192, 360582537790567680]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 42150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 42100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360568236858241180, 360568247859263883⟩, ⟨601898751233653956, 602212272527660058⟩, true⟩

def words06 : List Nat := [360582536918616734, 360582535853051003, 360582535066462386, 360582534365605948, 360582533664742801, 360582532480902104, 360582531004533588, 360582529963979508, 360582528923295919, 360582528444336866]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 42160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 42100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560871707345099, 360560882713832925⟩, ⟨912542558203282535, 912856309987661169⟩, true⟩

def words07 : List Nat := [360582528106212949, 360582527486385937, 360582526866475851, 360582526974048018, 360582526974537238, 360582526856418994, 360582526738245122, 360582526223185070, 360582525149223013, 360582524636781898]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 42170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 42100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580900586542946, 360580911598442270⟩, ⟨67708773609068591, 68022753677014733⟩, true⟩

def words08 : List Nat := [360582524172376484, 360582524436214669, 360582524436731022, 360582524370075132, 360582524303334448, 360582523715701072, 360582523765853828, 360582524071813980, 360582524072334645, 360582523894097094]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 42180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 42100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360641547891798193, 360641558909119220⟩, ⟨(-2491339990450552194), (-2491025781614565034)⟩, true⟩

def words09 : List Nat := [360582524150551321, 360582524445379443, 360582525300960978, 360582526059951027, 360582526287711316, 360582526515518984, 360582527304037911, 360582528462275264, 360582529861566427, 360582531260920965]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 42190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 42100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 42100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk421B
