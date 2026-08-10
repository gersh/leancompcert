import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk516A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk516B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk516A

def state06 : KState := ⟨⟨360604233037024372, 360604249823862133⟩, ⟨(-1153494244806685007), (-1152908282681208033)⟩, true⟩

def words05 : List Nat := [360581929553947135, 360581930017278107, 360581930384093239, 360581930940497930, 360581931403494863, 360581931866595309, 360581932098143191, 360581932156935210, 360581932589523679, 360581933022354590]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360582875951089271, 360582892744653508⟩, ⟨(-50062806026578046), (-49476496376942618)⟩, true⟩

def words06 : List Nat := [360581933619975059, 360581934112932910, 360581934342557008, 360581934572248613, 360581934708708300, 360581935050705018, 360581935161793094, 360581935272999736, 360581935273642507, 360581935215355122]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360648053594833188, 360648070395148671⟩, ⟨(-3418167607227350768), (-3417580948708849008)⟩, true⟩

def words07 : List Nat := [360581935525829153, 360581935836500850, 360581936520669440, 360581937215394951, 360581937582783560, 360581937950209711, 360581938545055184, 360581939451883324, 360581940732084869, 360581942012402423]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360617899134491875, 360617915941623455⟩, ⟨(-1859752056337316995), (-1859165045528945767)⟩, true⟩

def words08 : List Nat := [360581942981227758, 360581943576547040, 360581944545286230, 360581945514197906, 360581946389874210, 360581947039719488, 360581947501655010, 360581947963660717, 360581948344647600, 360581949041282411]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569873160686327, 360569889974548127⟩, ⟨623081370266510131, 623668728994363061⟩, true⟩

def words09 : List Nat := [360581950111132512, 360581951181078235, 360581952063614226, 360581952572814064, 360581952817510473, 360581953062383659, 360581953433522497, 360581953434237766, 360581953432069669, 360581953199480320]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk516B
