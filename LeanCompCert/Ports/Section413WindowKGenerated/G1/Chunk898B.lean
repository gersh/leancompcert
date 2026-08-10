import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk898A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk898B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk898A

def state06 : KState := ⟨⟨362463447192673357, 362463569364748395⟩, ⟨1929899148267628091, 1937311596765450981⟩, true⟩

def words05 : List Nat := [371285129547796177, 371285129540374371, 371285129531863965, 371285129518064766, 371285129338282308, 371285129197987496, 371285129055965703, 371285129016033173, 371285128822153141, 371285128585722861]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 89850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 89800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479918779137165, 362480040979260556⟩, ⟨449694569718844964, 457109538785821082⟩, true⟩

def words06 : List Nat := [371285128347934283, 371285128200325365, 371285128000042174, 371285127912515518, 371285127824008306, 371285127715295038, 371285127508257850, 371285127426543884, 371285127343251546, 371285127321074130]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 89860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 89800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362471470233207511, 362471592461946453⟩, ⟨1209019286641319053, 1216436827530312199⟩, true⟩

def words07 : List Nat := [371285127266823712, 371285127205335037, 371285127142566895, 371285127110650589, 371285127015322407, 371285126958095457, 371285126899839106, 371285126842220787, 371285126618641769, 371285126472043586]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 89870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 89800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362462691405862014, 362462813662506115⟩, ⟨1998120834110884164, 2005540883260040554⟩, true⟩

def words08 : List Nat := [371285126323607410, 371285126239428215, 371285126035917443, 371285125831899713, 371285125626708572, 371285125460589346, 371285125236813190, 371285125065692468, 371285124893476371, 371285124719167146]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 89880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 89800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490516033251236, 362490638318212610⟩, ⟨(-503171054361812524), (-495748459631621418)⟩, true⟩

def words09 : List Nat := [371285124473092481, 371285124352335413, 371285124229927949, 371285124221869216, 371285124110165711, 371285123989381753, 371285123867286337, 371285123870165714, 371285123871330987, 371285123936174239]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 89890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 89800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 89800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk898B
