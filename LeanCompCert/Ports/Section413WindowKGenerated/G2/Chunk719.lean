import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk719

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360605586723736223, 360605620113391310⟩, ⟨(-1675020684965772330), (-1673399123399055654)⟩, true⟩

def state01 : KState := ⟨⟨360589950147298684, 360589983546681030⟩, ⟨(-550826055372597671), (-549203794369042437)⟩, true⟩

def words00 : List Nat := [360582346683816225, 360582346717116367, 360582346807815294, 360582346898826803, 360582346917379578, 360582346918400194, 360582346793333670, 360582346521034171, 360582346248546878, 360582346275688150]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 71900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 71900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580472755058102, 360580506164065246⟩, ⟨130702244304205598, 132325197474842564⟩, true⟩

def words01 : List Nat := [360582346378733482, 360582346481957126, 360582346488591999, 360582346489613116, 360582346384747046, 360582346188207163, 360582345991367990, 360582346081963438, 360582346082881698, 360582346058357166]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 71910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 71900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574296703958511, 360574330122600356⟩, ⟨574961030924534926, 576584677070863430⟩, true⟩

def words02 : List Nat := [360582346033601922, 360582346090464521, 360582346305837439, 360582346521399720, 360582346551268804, 360582346552289649, 360582346389176415, 360582346292540868, 360582346195605847, 360582346036364723]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 71920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 71900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360561279190830936, 360561312619202147⟩, ⟨1511455492074394709, 1513079838102428823⟩, true⟩

def words03 : List Nat := [360582345925835503, 360582345719033714, 360582345512024179, 360582345601429623, 360582345656370990, 360582345711477295, 360582345712395567, 360582345670310760, 360582345435251232, 360582345144057616]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 71930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 71900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580422512913838, 360580455950897553⟩, ⟨134195102846743897, 135820140447102969⟩, true⟩

def words04 : List Nat := [360582344852525225, 360582344754098208, 360582344598276477, 360582344346197675, 360582344093955240, 360582343792972933, 360582343685791960, 360582343729241491, 360582343730152191, 360582343652641085]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 71940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 71900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360576092786871044, 360576126234506212⟩, ⟨445619760278327101, 447245492347491597⟩, true⟩

def words05 : List Nat := [360582343627237085, 360582343575927491, 360582343524335976, 360582343404208234, 360582343091308945, 360582342602599740, 360582342113708920, 360582341756303656, 360582341515637816, 360582341430342059]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 71950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 71900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360568293876228964, 360568327333588545⟩, ⟨1006787808335794169, 1008414240222227139⟩, true⟩

def words06 : List Nat := [360582341344885730, 360582341125247697, 360582340877432039, 360582340822717175, 360582340767723227, 360582340622534399, 360582340284600835, 360582339783443064, 360582339282098932, 360582338925088090]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 71960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 71900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579011229986350, 360579044696961835⟩, ⟨235443485685615038, 237070609676731080⟩, true⟩

def words07 : List Nat := [360582338731230236, 360582338730317478, 360582338729306004, 360582338581455420, 360582338496589138, 360582338363805350, 360582338251457810, 360582338302985892, 360582338303896197, 360582338259196855]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 71970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 71900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602718543669377, 360602752020303758⟩, ⟨(-1471195367243697971), (-1469567547958828909)⟩, true⟩

def words08 : List Nat := [360582338214285605, 360582338086054456, 360582338264161795, 360582338450162799, 360582338471792279, 360582338472813987, 360582338322511184, 360582338344424468, 360582338523648575, 360582338808263936]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 71980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 71900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594655305928246, 360594688792299822⟩, ⟨(-890678283824524270), (-889049763511985660)⟩, true⟩

def words09 : List Nat := [360582338973545618, 360582339138923572, 360582339496730262, 360582339985676893, 360582340269344262, 360582340553147591, 360582340725496311, 360582340726518130, 360582340877739959, 360582341050414127]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 71990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 71900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 71900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk719
