import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk592

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362463658516087687, 362463709846739406⟩, ⟨1260828131002992380, 1262880793212273910⟩, true⟩

def state01 : KState := ⟨⟨362497976606857048, 362498027955427273⟩, ⟨(-770941205205559928), (-768887482130316196)⟩, true⟩

def words00 : List Nat := [371285041933589617, 371285041822149123, 371285041724718433, 371285041804104434, 371285041840129991, 371285041842166599, 371285041725552304, 371285041811812178, 371285042182670752, 371285042404057928]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 59200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 59200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491497435332260, 362491548802165339⟩, ⟨(-387304696025540581), (-385249891517695367)⟩, true⟩

def words01 : List Nat := [371285042582769810, 371285042762113050, 371285042974823845, 371285043056952333, 371285043191601956, 371285043327032846, 371285043460404242, 371285043462408320, 371285043397893826, 371285043510266896]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 59210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 59200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474815522083288, 362474866906736198⟩, ⟨600727772835484070, 602783632727470670⟩, true⟩

def words02 : List Nat := [371285043907035015, 371285043924189169, 371285043935238096, 371285043946991568, 371285043980901855, 371285043983108376, 371285043882893842, 371285043892738298, 371285043903358725, 371285043905431580]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 59220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 59200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362508096354293293, 362508147757057712⟩, ⟨(-1370655777408906043), (-1368598844679652201)⟩, true⟩

def words03 : List Nat := [371285043802457760, 371285043872366700, 371285044226657378, 371285044345563491, 371285044370506442, 371285044396043759, 371285044642757811, 371285044749587901, 371285045140936621, 371285045533181011]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 59230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 59200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362499305793121908, 362499357213987452⟩, ⟨(-849905706024434494), (-847847700893076626)⟩, true⟩

def words04 : List Nat := [371285045898931666, 371285045971566704, 371285046328921093, 371285046687279303, 371285047032774877, 371285047124886291, 371285047180148955, 371285047236137902, 371285047545862067, 371285047789658866]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 59240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 59200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489005370650498, 362489056809511020⟩, ⟨(-239455169615303834), (-237396098187133880)⟩, true⟩

def words05 : List Nat := [371285048295157359, 371285048801435233, 371285049305671611, 371285049595633398, 371285049901360730, 371285050208083434, 371285050658164034, 371285050729098638, 371285050798198070, 371285050868028644]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 59250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 59200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492167787954714, 362492219244778105⟩, ⟨(-426775098360477682), (-424714962361396132)⟩, true⟩

def words06 : List Nat := [371285051144634502, 371285051340658354, 371285051820923068, 371285052302015036, 371285052740590691, 371285052799929929, 371285052986216549, 371285053173522170, 371285053476509077, 371285053599481731]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 59260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 59200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489255097446659, 362489306572561749⟩, ⟨(-254061004689319467), (-251999784454174163)⟩, true⟩

def words07 : List Nat := [371285053701136450, 371285053803481356, 371285054190048568, 371285054449793556, 371285054795263900, 371285055141509764, 371285055485684570, 371285055488440507, 371285055561525005, 371285055635761524]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 59270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 59200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485565065869279, 362485616558838776⟩, ⟨(-35303449079293791), (-33241170341433833)⟩, true⟩

def words08 : List Nat := [371285055993828334, 371285055995832773, 371285055974594227, 371285055892558251, 371285055809776122, 371285055791254861, 371285055728627483, 371285055816716977, 371285055902802540, 371285055914384451]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 59280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 59200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362498704066196101, 362498755577255113⟩, ⟨(-814350591532023624), (-812287240176914006)⟩, true⟩

def words09 : List Nat := [371285056185324232, 371285056457296701, 371285056915892216, 371285057070071091, 371285057145092690, 371285057220769445, 371285057387142681, 371285057412807681, 371285057645168473, 371285057878393764]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 59290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 59200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 59200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk592
