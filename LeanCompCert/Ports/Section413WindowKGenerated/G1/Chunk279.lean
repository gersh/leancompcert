import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk279

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476491921712582, 362476502642236848⟩, ⟨240809831718594249, 241012025339552011⟩, true⟩

def state01 : KState := ⟨⟨362454136337277339, 362454147065723682⟩, ⟨864832623467221230, 865035038156068966⟩, true⟩

def words00 : List Nat := [371285141729785445, 371285141730689557, 371285141640649874, 371285141496361489, 371285141595457799, 371285141596436961, 371285141200418706, 371285141145356543, 371285141090025314, 371285140796936727]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 27900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 27900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362520389214247846, 362520399950745856⟩, ⟨(-984708498850252426), (-984505859398281796)⟩, true⟩

def words01 : List Nat := [371285139687096398, 371285139171063325, 371285139245343429, 371285139246235095, 371285138526960394, 371285137601976043, 371285137032109591, 371285137033106089, 371285138278553971, 371285139542472575]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 27910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 27900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362465183649998269, 362465194394530171⟩, ⟨556811605097049675, 557014468896267355⟩, true⟩

def words02 : List Nat := [371285140629061776, 371285140629952553, 371285140601643213, 371285140854722968, 371285141508308637, 371285141509198326, 371285140455411182, 371285139294742589, 371285138133792908, 371285137626499247]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 27920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 27900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362401965561139198, 362401976313674637⟩, ⟨2322941857062515631, 2323144944441236355⟩, true⟩

def words03 : List Nat := [371285136913088126, 371285136752805557, 371285136592243444, 371285136431028949, 371285134563214333, 371285132884781416, 371285131206000157, 371285129817019078, 371285126924526114, 371285123949481410]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 27930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 27900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362452092857480988, 362452103617979869⟩, ⟨922233658754048253, 922436968671677687⟩, true⟩

def words04 : List Nat := [371285120974257217, 371285119278977843, 371285116945038782, 371285115890962533, 371285114836669175, 371285113477301418, 371285110598931265, 371285109000315746, 371285107401363311, 371285106729560252]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 27940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 27900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362470521624768128, 362470532393392799⟩, ⟨407025589118021664, 407229126193502564⟩, true⟩

def words05 : List Nat := [371285105549493749, 371285103935469267, 371285102321187948, 371285101985958650, 371285101015708294, 371285100431530839, 371285099847102970, 371285099261722832, 371285097617298145, 371285097097476973]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 27950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 27900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474565447435624, 362474576223994132⟩, ⟨294068082254672952, 294271841201044554⟩, true⟩

def words06 : List Nat := [371285097334062161, 371285097334959863, 371285097245660407, 371285097125450752, 371285097004930514, 371285096731606495, 371285096329131210, 371285096767129311, 371285097204166154, 371285097205088199]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 27960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 27900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501763686563698, 362501774471178903⟩, ⟨(-466745440101258703), (-466541455768705615)⟩, true⟩

def words07 : List Nat := [371285097567976022, 371285098307429678, 371285099698722317, 371285099699613648, 371285099588390059, 371285099255751268, 371285099663923377, 371285099768696154, 371285100365263029, 371285100962163189]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 27970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 27900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491970902968069, 362491981695636586⟩, ⟨(-192750758626866359), (-192546548921461199)⟩, true⟩

def words08 : List Nat := [371285101552486586, 371285101553380393, 371285101400993029, 371285101963380323, 371285102780154169, 371285102781061016, 371285102541149187, 371285102272623199, 371285102575321268, 371285102822108615]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 27980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 27900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362447368670552660, 362447379471268369⟩, ⟨1056026805072687154, 1056231240059737248⟩, true⟩

def words09 : List Nat := [371285103970977346, 371285105120132382, 371285106060227069, 371285106061118849, 371285105302024048, 371285104604633096, 371285104482907806, 371285104483799727, 371285103361805663, 371285102015556217]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 27990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 27900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 27900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk279
