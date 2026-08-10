import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk584A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk584B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk584A

def state06 : KState := ⟨⟨360620107612419314, 360620129325399656⟩, ⟨(-2230660220677679266), (-2229802654839818900)⟩, true⟩

def words05 : List Nat := [360581983429490991, 360581983744964662, 360581984352973457, 360581984919519633, 360581985235105804, 360581985550737216, 360581985855533668, 360581986306483165, 360581986959606657, 360581987612893202]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598353949215269, 360598375669970858⟩, ⟨(-959034687285299939), (-958176666867826477)⟩, true⟩

def words06 : List Nat := [360581988081629337, 360581988258598044, 360581988399426458, 360581988540511215, 360581988541198918, 360581988493594286, 360581988476540084, 360581988312276098, 360581988176875228, 360581988458073203]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587375929881189, 360587397658334621⟩, ⟨(-317116524551614986), (-316258054002904716)⟩, true⟩

def words07 : List Nat := [360581988730570462, 360581989003203399, 360581989106694820, 360581989146585089, 360581989147269059, 360581989111423379, 360581989331127283, 360581989594822725, 360581989688027182, 360581989781348884]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601290752168314, 360601312488326148⟩, ⟨(-1130823760446701037), (-1129964839305972193)⟩, true⟩

def words08 : List Nat := [360581990166999809, 360581990729059925, 360581991522967593, 360581992317004594, 360581992826997235, 360581993045392317, 360581993167403642, 360581993289642796, 360581993546819043, 360581993877953510]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582046551053669, 360582068295008612⟩, ⟨(-5102166833887006), (-4242789603456372)⟩, true⟩

def words09 : List Nat := [360581994008936540, 360581994140011591, 360581994427118038, 360581994860217803, 360581995218208760, 360581995576320821, 360581995691910425, 360581995765833014, 360581995767744860, 360581995769930350]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk584B
