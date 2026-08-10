import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk916A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk916B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk916A

def state06 : KState := ⟨⟨360561204168794273, 360561259472157516⟩, ⟨1896527594541950176, 1899950616840090162⟩, true⟩

def words05 : List Nat := [360581989097316818, 360581989088104322, 360581989078738580, 360581988998041337, 360581988798310980, 360581988535289063, 360581988271866663, 360581988103673411, 360581987938441414, 360581987713667882]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 91650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 91600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360565302650354174, 360565357966218316⟩, ⟨1520834221268692459, 1524258389460928735⟩, true⟩

def words06 : List Nat := [360581987488598750, 360581987349929971, 360581987270512765, 360581987152526316, 360581987034470067, 360581986795446424, 360581986437388857, 360581986152554791, 360581985867338736, 360581985634915392]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 91660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 91600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360562735130893165, 360562790459395707⟩, ⟨1756245879631248441, 1759671206448017773⟩, true⟩

def words07 : List Nat := [360581985454711700, 360581985214968808, 360581984974954054, 360581984854204152, 360581984822487344, 360581984732504353, 360581984642371358, 360581984492689675, 360581984288602456, 360581984080757488]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 91670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 91600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360558247735825645, 360558303076803400⟩, ⟨2167617055592368480, 2171043526197927560⟩, true⟩

def words08 : List Nat := [360581983872479306, 360581983704468785, 360581983417579698, 360581983057152511, 360581982696524546, 360581982259630259, 360581981929839364, 360581981698644536, 360581981467315588, 360581981160849621]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 91680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 91600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360581066289199015, 360581121642706965⟩, ⟨75232527970549012, 78660147529687972⟩, true⟩

def words09 : List Nat := [360581980903683040, 360581980765726086, 360581980627386283, 360581980486597945, 360581980308569871, 360581980029519134, 360581979750211749, 360581979552268061, 360581979449437155, 360581979441480463]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 91690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 91600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 91600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk916B
