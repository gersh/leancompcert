import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk648A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk648B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk648A

def state06 : KState := ⟨⟨360557113729334396, 360557140678562812⟩, ⟨1673789919541006849, 1674970666092549463⟩, true⟩

def words05 : List Nat := [360582967490698489, 360582967158826395, 360582966826789042, 360582966757691719, 360582966758471414, 360582966571851763, 360582966385135918, 360582966049585620, 360582965476947360, 360582965079828501]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 64850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 64800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360568477529961861, 360568504487801192⟩, ⟨936702452677299164, 937883757776457928⟩, true⟩

def words06 : List Nat := [360582964682417438, 360582964424224711, 360582964244999052, 360582963946556653, 360582963647974557, 360582963290132580, 360582963081181648, 360582962909934341, 360582962738606927, 360582962384483426]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 64860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 64800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360609689495880115, 360609716462338785⟩, ⟨(-1736985946203658227), (-1735804081925437523)⟩, true⟩

def words07 : List Nat := [360582962176632625, 360582962191933149, 360582962334488332, 360582962335401859, 360582962295459166, 360582962052198119, 360582961808753535, 360582961977972629, 360582962391079958, 360582962804381519]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 64870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 64800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360552750675427984, 360552777650609970⟩, ⟨1957368476232840789, 1958550906521667187⟩, true⟩

def words08 : List Nat := [360582963088390183, 360582963135688557, 360582963136445308, 360582963014779906, 360582962892877888, 360582962660951127, 360582962192154092, 360582961583003999, 360582960973704792, 360582960281316114]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 64880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 64800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360523387948041737, 360523414931822832⟩, ⟨3862957072348192984, 3864140060676914438⟩, true⟩

def words09 : List Nat := [360582959816926798, 360582959589754186, 360582959362489057, 360582958979997744, 360582958432366906, 360582957825516966, 360582957218425959, 360582956554335844, 360582955756778392, 360582954840307839]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 64890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 64800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 64800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk648B
