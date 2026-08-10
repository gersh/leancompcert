import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk731A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360618874363824435, 360618908922740892⟩, ⟨(-2668022198320365669), (-2666315863309170453)⟩, true⟩

def state01 : KState := ⟨⟨360608734392987698, 360608768961803058⟩, ⟨(-1926881693289003342), (-1925174634617846930)⟩, true⟩

def words00 : List Nat := [360582434858059891, 360582435016922003, 360582435287455345, 360582435558285673, 360582435781395131, 360582435977802121, 360582436079762689, 360582436181843351, 360582436384573524, 360582436745931058]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 73100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 73100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360565192245892295, 360565226824490660⟩, ⟨1256805986886291864, 1258513760842045862⟩, true⟩

def words01 : List Nat := [360582437260605860, 360582437775473140, 360582438196898177, 360582438475330857, 360582438625019231, 360582438774975355, 360582438820414138, 360582438821453166, 360582438680262729, 360582438445946378]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 73110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 73100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590665528243445, 360590700116663070⟩, ⟨(-605851586267526890), (-604143094133609770)⟩, true⟩

def words02 : List Nat := [360582438211401085, 360582438258229557, 360582438497099790, 360582438736162417, 360582438815162499, 360582438816201607, 360582438786471070, 360582438865706765, 360582438894554318, 360582439008594897]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 73120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 73100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596358300668839, 360596392898987714⟩, ⟨(-1022176647922027345), (-1020467431808241961)⟩, true⟩

def words03 : List Nat := [360582439009522896, 360582439009159204, 360582439193913480, 360582439515415281, 360582439789222525, 360582440063209755, 360582440243817685, 360582440458011577, 360582440649621320, 360582440841567003]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 73130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 73100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604874426147725, 360604909034266560⟩, ⟨(-1645158354735497060), (-1643448421806697900)⟩, true⟩

def words04 : List Nat := [360582441219841579, 360582441411678209, 360582441449747271, 360582441487902734, 360582441488772746, 360582441575664139, 360582441825235875, 360582442074999768, 360582442205795068, 360582442514030245]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 73140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 73100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk731A
