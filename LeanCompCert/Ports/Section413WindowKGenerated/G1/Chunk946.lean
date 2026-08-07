import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk946

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485502711989718, 362485638652179791⟩, ⟨(-52041724992081500), (-43359139789973376)⟩, true⟩

def state01 : KState := ⟨⟨362489060723306670, 362489196693135791⟩, ⟨(-388629329650385730), (-379943940445603652)⟩, true⟩

def words00 : List Nat := [371285180373726059, 371285180377977537, 371285180492647979, 371285180608636351, 371285180687734458, 371285180691048600, 371285180647223056, 371285180677666013, 371285180793494447, 371285180839372005]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 94600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 94600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485105952594971, 362485241952603512⟩, ⟨(-14421700723977966), (-5733456091676422)⟩, true⟩

def words01 : List Nat := [371285180852308602, 371285180866382285, 371285180990868499, 371285181074138594, 371285181179747900, 371285181286655012, 371285181392897617, 371285181396212292, 371285181353976931, 371285181358696328]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 94610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 94600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487240504335352, 362487376533884042⟩, ⟨(-216353423252936644), (-207662383378249082)⟩, true⟩

def words02 : List Nat := [371285181473364574, 371285181528402386, 371285181582212744, 371285181637189400, 371285181723918688, 371285181771892372, 371285181868790297, 371285181966995164, 371285182063756716, 371285182090378444]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 94620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 94600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490695372554194, 362490831432139442⟩, ⟨(-543301855546382650), (-534607973162862002)⟩, true⟩

def words03 : List Nat := [371285182216629513, 371285182344627932, 371285182484054689, 371285182487369868, 371285182478229484, 371285182453393828, 371285182493516523, 371285182507788293, 371285182569735461, 371285182633276763]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 94630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 94600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479300904277056, 362479436993734428⟩, ⟨535086607446858786, 543783317081865764⟩, true⟩

def words04 : List Nat := [371285182695093959, 371285182698409762, 371285182625152618, 371285182622549724, 371285182624680142, 371285182627997522, 371285182507524677, 371285182366573639, 371285182224245553, 371285182195182731]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 94640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 94600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481703042159241, 362481839161441319⟩, ⟨307751172407036666, 316450705100646536⟩, true⟩

def words05 : List Nat := [371285182187754543, 371285182242344553, 371285182292833881, 371285182296207559, 371285182253754660, 371285182219043863, 371285182242116337, 371285182245441403, 371285182217625927, 371285182186003972]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 94650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 94600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362493521545339624, 362493657694338544⟩, ⟨(-811039967425798629), (-802337621584607277)⟩, true⟩

def words06 : List Nat := [371285182163904165, 371285182167596581, 371285182185390213, 371285182248734489, 371285182294019499, 371285182297374383, 371285182349309546, 371285182429124648, 371285182591913008, 371285182684868014]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 94660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 94600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485134832362614, 362485271011616622⟩, ⟨(-17007175923260213), (-8301965681952477)⟩, true⟩

def words07 : List Nat := [371285182764892642, 371285182846057258, 371285182996156865, 371285183099048900, 371285183204235542, 371285183310617744, 371285183389149275, 371285183392466005, 371285183322967023, 371285183328072068]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 94670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 94600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485188625620281, 362485324834447723⟩, ⟨(-22074933844841719), (-13366923437536299)⟩, true⟩

def words08 : List Nat := [371285183431339350, 371285183442995383, 371285183445475330, 371285183446369517, 371285183466086285, 371285183469743372, 371285183522630664, 371285183607432062, 371285183665902864, 371285183670837269]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 94680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 94600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497332613502257, 362497468852275465⟩, ⟨(-1172040968680951119), (-1163330122558433627)⟩, true⟩

def words09 : List Nat := [371285183749225734, 371285183829313352, 371285184019306343, 371285184075662673, 371285184105096744, 371285184135664538, 371285184266847245, 371285184343595864, 371285184475580649, 371285184608998642]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 94690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 94600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 94600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk946
