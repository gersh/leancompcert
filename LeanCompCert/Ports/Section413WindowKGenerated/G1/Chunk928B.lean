import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk928A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk928B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk928A

def state06 : KState := ⟨⟨362481220538554883, 362481351335751550⟩, ⟨341963295108304767, 350163812268157657⟩, true⟩

def words05 : List Nat := [371285122110566762, 371285122198807503, 371285122284330522, 371285122287587406, 371285122254292963, 371285122227957397, 371285122285653145, 371285122288904149, 371285122251615498, 371285122214625858]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 92850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 92800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362493732851770862, 362493863678071390⟩, ⟨(-819935975311135428), (-811732755421286736)⟩, true⟩

def words06 : List Nat := [371285122251608178, 371285122301418284, 371285122465719901, 371285122631387686, 371285122766869412, 371285122770118425, 371285122874754851, 371285122987815567, 371285123147567094, 371285123245046859]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 92860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 92800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491723489903211, 362491854345883807⟩, ⟨(-633314543208476450), (-625108566793078732)⟩, true⟩

def words07 : List Nat := [371285123325588210, 371285123407251200, 371285123546681273, 371285123638827256, 371285123764493090, 371285123891433460, 371285124015249275, 371285124018498251, 371285124060042001, 371285124136618263]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 92870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 92800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486150287147609, 362486281172088294⟩, ⟨(-115645056531473339), (-107436390149990595)⟩, true⟩

def words08 : List Nat := [371285124322083129, 371285124354099889, 371285124362747972, 371285124372446002, 371285124401125013, 371285124404706338, 371285124442592408, 371285124506912775, 371285124570644722, 371285124586518648]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 92880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 92800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496287805159485, 362496418719425086⟩, ⟨(-1057370288103543249), (-1049158897578300355)⟩, true⟩

def words09 : List Nat := [371285124685688280, 371285124786502067, 371285125001568085, 371285125063224642, 371285125086317047, 371285125110450500, 371285125160789588, 371285125170097041, 371285125293867007, 371285125419056110]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 92890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 92800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 92800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk928B
