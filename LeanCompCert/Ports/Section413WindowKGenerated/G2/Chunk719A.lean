import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk719A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk719A
