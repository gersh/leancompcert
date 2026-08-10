import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk382A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk382B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk382A

def state06 : KState := ⟨⟨360581096260333363, 360581105244404030⟩, ⟨31082009681913889, 31314350167240955⟩, true⟩

def words05 : List Nat := [360581921897631026, 360581922918563141, 360581923504574040, 360581923694528202, 360581923694968034, 360581923417342256, 360581923328889588, 360581923726639292, 360581923727106375, 360581923706248443]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360624649170962603, 360624658159915740⟩, ⟨(-1635277012962867915), (-1635044485650078161)⟩, true⟩

def words06 : List Nat := [360581924345448157, 360581925540461152, 360581927251470992, 360581928962490297, 360581930090767625, 360581931063438246, 360581932261617456, 360581933459889443, 360581934237623388, 360581935354510863]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360623501534773899, 360623510528646516⟩, ⟨(-1591309702587086738), (-1591076986980947676)⟩, true⟩

def words07 : List Nat := [360581936129500056, 360581936904508461, 360581938360473213, 360581940155468549, 360581941770748596, 360581943386037001, 360581944660662717, 360581945257200014, 360581946343440139, 360581947429799022]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360629073132565074, 360629082131310659⟩, ⟨(-1804738388715674586), (-1804505486547722206)⟩, true⟩

def words08 : List Nat := [360581949196740358, 360581950285684613, 360581950848892371, 360581951412120732, 360581951472242204, 360581951879288231, 360581952966790912, 360581954054335757, 360581954800221856, 360581956031534009]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360647444943150271, 360647453946772905⟩, ⟨(-2508421962385351499), (-2508188873450607927)⟩, true⟩

def words09 : List Nat := [360581957220343448, 360581958409239260, 360581960106096629, 360581961408514147, 360581962027107584, 360581962645703921, 360581963245375411, 360581964275763460, 360581965986094736, 360581967696454360]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk382B
