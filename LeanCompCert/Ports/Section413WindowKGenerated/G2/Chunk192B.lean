import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk192A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk192B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk192A

def state06 : KState := ⟨⟨360550749103078977, 360550751248974719⟩, ⟨645495820100042085, 645523792715493247⟩, true⟩

def words05 : List Nat := [360584276001093739, 360584274941931854, 360584273882834022, 360584274652927404, 360584275043800547, 360584275434673408, 360584275434896424, 360584273700882822, 360584269281441124, 360584267541431391]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360528752542165780, 360528754690379497⟩, ⟨1068787808158150834, 1068815825429553368⟩, true⟩

def words06 : List Nat := [360584265801520723, 360584262942662658, 360584257399068861, 360584250513983250, 360584243629568138, 360584236066877418, 360584230372335653, 360584227355174176, 360584224338300977, 360584219964143356]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602598047884868, 360602600198427566⟩, ⟨(-354761937159912717), (-354733874997951069)⟩, true⟩

def words07 : List Nat := [360584217086172957, 360584214146682802, 360584211207424222, 360584210943628935, 360584209571427370, 360584205885736934, 360584202200381977, 360584200183708279, 360584201138266182, 360584202092779625]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360530607995129102, 360530610148015027⟩, ⟨1033073138005724558, 1033101245357070042⟩, true⟩

def words08 : List Nat := [360584202092999093, 360584201708357010, 360584199866292088, 360584198434816637, 360584197003428961, 360584193314018128, 360584186946706727, 360584179226862232, 360584171507771207, 360584166459334730]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360425216313864134, 360425218469076148⟩, ⟨3066946873648573609, 3066975025881844451⟩, true⟩

def words09 : List Nat := [360584163683301270, 360584162722833642, 360584161762433357, 360584159174474150, 360584156244173100, 360584151581950731, 360584146920137612, 360584143460593180, 360584137326060988, 360584129092178835]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk192B
