import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk564A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk564B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk564A

def state06 : KState := ⟨⟨360540358083767813, 360540378280065810⟩, ⟨2334414301579630744, 2335184709382595190⟩, true⟩

def words05 : List Nat := [360581741282976464, 360581740853301176, 360581740423485268, 360581740376737883, 360581740377407309, 360581740234183011, 360581740090887381, 360581739699914534, 360581738995961586, 360581738264291503]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 56450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 56400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360551853753543856, 360551873957255575⟩, ⟨1685338393622252985, 1686109220041068563⟩, true⟩

def words06 : List Nat := [360581737532386536, 360581737043924494, 360581736657851864, 360581735985888155, 360581735313820917, 360581734474989152, 360581733794756427, 360581733427831427, 360581733060844091, 360581732452386460]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 56460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 56400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360618725981355759, 360618746192490473⟩, ⟨(-2091307306115685216), (-2090536060483558398)⟩, true⟩

def words07 : List Nat := [360581731924282138, 360581731637418495, 360581731375688440, 360581731520114776, 360581731520847660, 360581731393880328, 360581731452033555, 360581731795238550, 360581732451228607, 360581733107373646]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 56470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 56400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593415640727955, 360593435859366336⟩, ⟨(-661848661384832255), (-661076991909111821)⟩, true⟩

def words08 : List Nat := [360581733576111851, 360581733861299541, 360581734137987137, 360581734414893433, 360581734419123802, 360581734419910806, 360581734208826848, 360581733805032291, 360581733401100247, 360581733517543584]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 56480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 56400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360565477867587580, 360565498093633902⟩, ⟨916527291817407522, 917299379804958236⟩, true⟩

def words09 : List Nat := [360581733828902920, 360581734140400958, 360581734294829103, 360581734295616354, 360581734246992625, 360581734119272169, 360581733991330849, 360581733852544141, 360581733767428509, 360581733480887088]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 56490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 56400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 56400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk564B
