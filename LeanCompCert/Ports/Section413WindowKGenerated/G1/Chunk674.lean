import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk674

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489138980798806, 362489206199703931⟩, ⟨(-252760682486268704), (-249700782373833338)⟩, true⟩

def state01 : KState := ⟨⟨362470122172623487, 362470189412332522⟩, ⟨1029000438975452368, 1032061741376212576⟩, true⟩

def words00 : List Nat := [371285501550935293, 371285501553236515, 371285501347592198, 371285501235046743, 371285501121403365, 371285501013555994, 371285500611946686, 371285500211481144, 371285499810043963, 371285499629531398]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 67400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 67400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362457574525723098, 362457641786104294⟩, ⟨1874982514226385233, 1878045210245629823⟩, true⟩

def words01 : List Nat := [371285499403974663, 371285499399117103, 371285499393500740, 371285499368683113, 371285499088851418, 371285498849638936, 371285498609247038, 371285498461533607, 371285498103127963, 371285497692515532]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 67410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 67400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482297687849390, 362482364968834752⟩, ⟨208049282791642814, 211113368047078392⟩, true⟩

def words02 : List Nat := [371285497280912853, 371285497090029997, 371285496807886147, 371285496727768815, 371285496646864025, 371285496540556815, 371285496140493725, 371285495961314985, 371285495818698309, 371285495821097055]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 67420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 67400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487737159452938, 362487804461442361⟩, ⟨(-158747651589783365), (-155682149922780867)⟩, true⟩

def words03 : List Nat := [371285495776429413, 371285495699420665, 371285495761584546, 371285495794276671, 371285495893204483, 371285495992993857, 371285496072010902, 371285496074353068, 371285496004378777, 371285496041491252]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 67430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 67400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475080081371079, 362475147403846342⟩, ⟨694889907695900843, 697956791035595527⟩, true⟩

def words04 : List Nat := [371285496190280946, 371285496192583098, 371285496048636392, 371285495905779859, 371285495762084386, 371285495599827008, 371285495327003313, 371285495274685784, 371285495221571965, 371285495169465847]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 67440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 67400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488932545866755, 362488999889168964⟩, ⟨(-239480909205448500), (-236412620985797228)⟩, true⟩

def words05 : List Nat := [371285495035405079, 371285495055989419, 371285495294835343, 371285495297140016, 371285495298633950, 371285495266409127, 371285495343877057, 371285495347130566, 371285495400671809, 371285495455185095]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 67450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 67400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476990007833817, 362477057371902379⟩, ⟨566178024814961868, 569247714038538314⟩, true⟩

def words06 : List Nat := [371285495520559641, 371285495522862766, 371285495321739490, 371285495234835452, 371285495146749155, 371285495105692532, 371285494910653618, 371285494708147670, 371285494504735248, 371285494421169291]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 67460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 67400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472500788246739, 362472568173095113⟩, ⟨869149396479052662, 872220487823795004⟩, true⟩

def words07 : List Nat := [371285494375196821, 371285494455236560, 371285494470228205, 371285494472547443, 371285494290468231, 371285494176159290, 371285494163021372, 371285494165325118, 371285493976807669, 371285493787911708]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 67470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 67400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478885282612208, 362478952688082805⟩, ⟨438327637634982043, 441400120669905595⟩, true⟩

def words08 : List Nat := [371285493625741574, 371285493628307644, 371285493603459486, 371285493641370477, 371285493643165101, 371285493614425061, 371285493329159341, 371285493119559063, 371285492915661142, 371285492918052726]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 67480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 67400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486674754722112, 362486742181177277⟩, ⟨(-87397751563070074), (-84323852176826588)⟩, true⟩

def words09 : List Nat := [371285492822885946, 371285492727465220, 371285492752528682, 371285492797690848, 371285492908903547, 371285493021045883, 371285493114439296, 371285493116743843, 371285492936062127, 371285492957429824]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 67490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 67400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 67400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk674
