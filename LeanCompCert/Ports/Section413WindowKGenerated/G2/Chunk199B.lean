import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk199A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk199B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk199A

def state06 : KState := ⟨⟨360435630112777457, 360435632424864651⟩, ⟨2924149869270508305, 2924181101271221373⟩, true⟩

def words05 : List Nat := [360582175805471530, 360582173534409444, 360582171263549033, 360582167714772508, 360582163851582880, 360582158555120066, 360582153259117050, 360582147905697661, 360582141823932255, 360582134484046576]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360544975281702734, 360544977596203675⟩, ⟨741265829037548765, 741297109228622605⟩, true⟩

def words06 : List Nat := [360582127144838719, 360582122303882001, 360582118704867541, 360582117603457053, 360582116502133485, 360582112931825844, 360582107889365812, 360582104278060542, 360582100667041579, 360582098132469505]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360575877040515127, 360575879357456632⟩, ⟨123817551030206906, 123848879971382844⟩, true⟩

def words07 : List Nat := [360582096273981380, 360582092487583975, 360582088701516903, 360582087410361635, 360582087401912972, 360582085724073864, 360582084046373106, 360582081113415698, 360582078310061350, 360582078000097843]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360474135351193600, 360474137670543691⟩, ⟨2156989090917885315, 2157020467994955275⟩, true⟩

def words08 : List Nat := [360582077690079259, 360582076887143054, 360582074627073844, 360582071112953840, 360582067599147461, 360582062315909761, 360582058312032607, 360582053513318933, 360582048715058951, 360582042646431383]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360607149620393457, 360607151942165353⟩, ⟨(-502563668871387759), (-502532243370643307)⟩, true⟩

def words09 : List Nat := [360582037248960850, 360582034342824142, 360582031436897954, 360582031021778145, 360582029929312764, 360582026708793844, 360582023488548137, 360582024073127129, 360582025329731418, 360582026586264616]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk199B
