import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk592A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk592B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk592A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk592B
