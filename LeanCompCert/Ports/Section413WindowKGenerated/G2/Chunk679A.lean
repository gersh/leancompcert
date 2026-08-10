import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk679A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360555260476140209, 360555290118812386⟩, ⟨1868557816666263826, 1869917387284762540⟩, true⟩

def state01 : KState := ⟨⟨360571217328335791, 360571246980051638⟩, ⟨785047193675635721, 786407378405894441⟩, true⟩

def words00 : List Nat := [360582828998062326, 360582828810199125, 360582828731220146, 360582828685745778, 360582828640207113, 360582828410447169, 360582828086191057, 360582827716034989, 360582827345608554, 360582827121097227]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 67900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 67900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571378607398400, 360571408268253557⟩, ⟨774111338353688709, 775472143778998691⟩, true⟩

def words01 : List Nat := [360582826951432623, 360582826673342252, 360582826395071787, 360582826387492276, 360582826388297714, 360582826341460243, 360582826294519437, 360582826139188590, 360582825869653067, 360582825702643708]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 67910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 67900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360550816755344175, 360550846425244350⟩, ⟨2170674761955860128, 2172036181765059854⟩, true⟩

def words02 : List Nat := [360582825535334914, 360582825313517613, 360582824875083728, 360582824327793604, 360582823780375013, 360582823038754869, 360582822405897795, 360582821989724933, 360582821573442907, 360582821048853434]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 67920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 67900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585559813522583, 360585589492481738⟩, ⟨(-189629409763089036), (-188267374533800540)⟩, true⟩

def words03 : List Nat := [360582820578936641, 360582820325770665, 360582820072316369, 360582820035488181, 360582819782159301, 360582819325811201, 360582818869286590, 360582818542600517, 360582818408553756, 360582818450334378]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 67930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 67900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575851528602524, 360575881216722355⟩, ⟨470011963020760614, 471374620670080760⟩, true⟩

def words04 : List Nat := [360582818451197464, 360582818390620352, 360582818614305448, 360582818838267841, 360582818978780795, 360582818979740969, 360582818975077599, 360582818780915147, 360582818586590259, 360582818297232585]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 67940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 67900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk679A
