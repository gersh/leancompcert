import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk644A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk644B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk644A

def state06 : KState := ⟨⟨360643884650474103, 360643911255104442⟩, ⟨(-3932058276642139308), (-3930899811860912562)⟩, true⟩

def words05 : List Nat := [360582924134453415, 360582924549001924, 360582925203735557, 360582925901374088, 360582926395479340, 360582926889655705, 360582927537003362, 360582928305941907, 360582929252734179, 360582930199708763]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 64450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 64400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360615226243498997, 360615252856776012⟩, ⟨(-2084726975718241075), (-2083567953530139379)⟩, true⟩

def words06 : List Nat := [360582931025531944, 360582931667999665, 360582932304209540, 360582932940655699, 360582933516082993, 360582933852003406, 360582934011585873, 360582934171248605, 360582934444780000, 360582934947118490]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 64460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 64400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567291258588558, 360567317880403685⟩, ⟨1005932289942398846, 1007091862626029676⟩, true⟩

def words07 : List Nat := [360582935486520050, 360582936026073676, 360582936444599757, 360582936623627559, 360582936739724846, 360582936856068328, 360582936911659255, 360582936912566650, 360582936792014235, 360582936550729772]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 64470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 64400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360609623644230613, 360609650274605743⟩, ⟨(-1723879907056765315), (-1722719782380812415)⟩, true⟩

def words08 : List Nat := [360582936309244111, 360582936174146282, 360582936439515561, 360582936705066732, 360582936762394503, 360582936763303865, 360582936828999801, 360582936943702313, 360582937298284550, 360582937713436265]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 64480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 64400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360607279603272851, 360607306242304796⟩, ⟨(-1572829490835757185), (-1571668807840053091)⟩, true⟩

def words09 : List Nat := [360582937924431733, 360582938135506451, 360582938225182985, 360582938436183493, 360582938586253494, 360582938736467721, 360582938765832597, 360582938904485046, 360582939283007049, 360582939661820152]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 64490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 64400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 64400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk644B
