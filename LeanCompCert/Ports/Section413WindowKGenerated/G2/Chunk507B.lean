import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk507A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk507B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk507A

def state06 : KState := ⟨⟨360583520030316657, 360583536214097325⟩, ⟨(-77399516074644217), (-76844437350906231)⟩, true⟩

def words05 : List Nat := [360582022460160551, 360582022117032562, 360582021817346911, 360582022156240855, 360582022397758186, 360582022639380415, 360582022640016144, 360582022583853222, 360582022335484708, 360582022366116574]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 50700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583692311506337, 360583708501892857⟩, ⟨(-86182967936201743), (-85627553865902523)⟩, true⟩

def words06 : List Nat := [360582022575519645, 360582022658125661, 360582022658750690, 360582022547243568, 360582022435620641, 360582021983937503, 360582021857656572, 360582021988495166, 360582021989126118, 360582021957332658]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 50760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 50700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360605541035084870, 360605557232106825⟩, ⟨(-1195602642990528728), (-1195046892006850946)⟩, true⟩

def words07 : List Nat := [360582021981696963, 360582022006256183, 360582022417638470, 360582022568790409, 360582022569438228, 360582022396188475, 360582022435847954, 360582022956957400, 360582023420982501, 360582023885146213]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 50770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 50700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581883254877819, 360581899458575810⟩, ⟨5667120966962158, 6223210993457840⟩, true⟩

def words08 : List Nat := [360582024155192141, 360582024155893992, 360582024166484220, 360582024294552097, 360582024295149711, 360582024153042487, 360582023750371306, 360582023033575940, 360582022316674481, 360582021986848964]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 50780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 50700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360551689471497219, 360551705681816080⟩, ⟨1539400292345477108, 1539956718678691930⟩, true⟩

def words09 : List Nat := [360582022097016586, 360582022209735989, 360582022210361363, 360582022129205384, 360582021754641463, 360582021283407315, 360582020811976778, 360582020627599166, 360582020386470054, 360582019790451488]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 50790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 50700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 50700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk507B
