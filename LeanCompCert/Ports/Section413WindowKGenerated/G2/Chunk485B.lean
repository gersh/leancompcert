import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk485A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk485B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk485A

def state06 : KState := ⟨⟨360586377399460101, 360586392157347076⟩, ⟨(-206537935837440196), (-206053679476503738)⟩, true⟩

def words05 : List Nat := [360582149883289572, 360582149719330509, 360582149587890758, 360582149588563717, 360582149562767469, 360582149176089174, 360582148789298762, 360582148788666082, 360582148876600048, 360582148964672368]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 48550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 48500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577315142211667, 360577329906463110⟩, ⟨233413653840953216, 233898219292268416⟩, true⟩

def words06 : List Nat := [360582148965267817, 360582148842286135, 360582148295143477, 360582148170863466, 360582148046406856, 360582147642771361, 360582147253800459, 360582146653976238, 360582146054046967, 360582145599674810]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 48560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 48500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360543960827408230, 360543975597962545⟩, ⟨1853694879991882280, 1854179751605129550⟩, true⟩

def words07 : List Nat := [360582145824422097, 360582146148431666, 360582146149043703, 360582146138639157, 360582145835421041, 360582145309179281, 360582144782757643, 360582144510822582, 360582143936491570, 360582143151515554]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 48570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 48500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360553249416395604, 360553264193259533⟩, ⟨1402346341896034165, 1402831520061874025⟩, true⟩

def words08 : List Nat := [360582142366411326, 360582141514623593, 360582140875195807, 360582140421424060, 360582139967619105, 360582139125281954, 360582138150445317, 360582136952883577, 360582135755175085, 360582134979842408]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 48580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 48500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572665794269996, 360572680577510355⟩, ⟨458808808668464591, 459294296695742179⟩, true⟩

def words09 : List Nat := [360582134386284661, 360582133577993648, 360582132769607771, 360582132383590150, 360582132349611667, 360582132210138968, 360582132070598915, 360582131662514206, 360582131271129542, 360582131077442367]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 48590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 48500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 48500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk485B
