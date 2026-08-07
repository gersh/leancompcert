import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk731

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

def state06 : KState := ⟨⟨360609587217506212, 360609621835426033⟩, ⟨(-1989988919753963483), (-1988278269833993587)⟩, true⟩

def words05 : List Nat := [360582442782706500, 360582443051684785, 360582443471372867, 360582443753923460, 360582443876689872, 360582443999533666, 360582444115175025, 360582444339695577, 360582444712016485, 360582445084563771]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587495466510312, 360587530094344739⟩, ⟨(-373758668417177094), (-372047293098209376)⟩, true⟩

def words06 : List Nat := [360582445315163052, 360582445404627918, 360582445580724985, 360582445757146633, 360582445885941609, 360582445886981326, 360582445829320570, 360582445657849280, 360582445486182676, 360582445466649366]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360559285739091497, 360559320376726028⟩, ⟨1690482500501861960, 1692194592945174100⟩, true⟩

def words07 : List Nat := [360582445532844077, 360582445599228387, 360582445600154894, 360582445573397602, 360582445359993964, 360582445100188378, 360582444840088950, 360582444628384837, 360582444422069368, 360582444107157091]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600238663650579, 360600273311102600⟩, ⟨(-1306694907938473661), (-1304982097003996695)⟩, true⟩

def words08 : List Nat := [360582443792017884, 360582443663644213, 360582443629055203, 360582443623290096, 360582443617464301, 360582443404574081, 360582443208575034, 360582443160719647, 360582443249944282, 360582443494636040]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587876438401103, 360587911095766538⟩, ⟨(-401788529522751039), (-400074992975800901)⟩, true⟩

def words09 : List Nat := [360582443634025098, 360582443773541081, 360582444041121375, 360582444448326672, 360582444807955993, 360582445167745951, 360582445433855695, 360582445513687762, 360582445589209946, 360582445665062371]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk731
