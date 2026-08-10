import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk890A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk890B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk890A

def state06 : KState := ⟨⟨360589083333463777, 360589135427321699⟩, ⟨(-631595150758539503), (-628462160944888525)⟩, true⟩

def words05 : List Nat := [360582078938973399, 360582078918028216, 360582078896708410, 360582078886850171, 360582078879791103, 360582078764053243, 360582078656918619, 360582078730391397, 360582078810666026, 360582078891229079]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 89050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 89000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561737487727302, 360561789593827804⟩, ⟨1803821393097601660, 1806955473297483750⟩, true⟩

def words06 : List Nat := [360582078892392905, 360582078876228803, 360582078733955877, 360582078547660565, 360582078361015868, 360582078123182898, 360582077759356954, 360582077300414964, 360582076841214803, 360582076508314135]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 89060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 89000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360548958936419075, 360549011054610673⟩, ⟨2942106426423280391, 2945241583638003993⟩, true⟩

def words07 : List Nat := [360582076281590916, 360582076180981037, 360582076080242434, 360582075914895453, 360582075623509977, 360582075245632993, 360582074867380489, 360582074596908948, 360582074307059474, 360582073937228972]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 89070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 89000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565283873113154, 360565336003441165⟩, ⟨1487883463181999857, 1491019701567753885⟩, true⟩

def words08 : List Nat := [360582073567111744, 360582073300969138, 360582073136970393, 360582073099046153, 360582073061023022, 360582072916311412, 360582072645537660, 360582072500966515, 360582072356050562, 360582072109643520]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 89080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 89000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554260013851930, 360554312156423382⟩, ⟨2470052176044887597, 2473189505256020913⟩, true⟩

def words09 : List Nat := [360582071922947034, 360582071658091374, 360582071392996181, 360582071174044005, 360582071023885844, 360582070824059154, 360582070624076463, 360582070337276622, 360582069924437349, 360582069614394831]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 89090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 89000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 89000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk890B
