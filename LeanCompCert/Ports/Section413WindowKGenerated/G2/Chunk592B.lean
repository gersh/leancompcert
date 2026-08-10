import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk592A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk592B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk592A

def state06 : KState := ⟨⟨360591144121637483, 360591166457082482⟩, ⟨(-542127690830929202), (-541233486174052438)⟩, true⟩

def words05 : List Nat := [360582028864250692, 360582029706615992, 360582030405374169, 360582031139276898, 360582031679523100, 360582032219967123, 360582032802059461, 360582033100450055, 360582033255311106, 360582033410286545]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 59250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 59200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601357395385197, 360601379738659502⟩, ⟨(-1147311019385384377), (-1146416350725280719)⟩, true⟩

def words06 : List Nat := [360582033688498651, 360582034213777976, 360582035023609013, 360582035833571579, 360582036400682150, 360582036684063331, 360582036947875652, 360582037211924939, 360582037467670120, 360582037794863628]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 59260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 59200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587711550215050, 360587733901379456⟩, ⟨(-338374995121392802), (-337479858777784600)⟩, true⟩

def words07 : List Nat := [360582037941048305, 360582038087318312, 360582038518175490, 360582039138462856, 360582039685396157, 360582040232460800, 360582040636052807, 360582040823641404, 360582040920354411, 360582041017339414]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 59270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 59200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597496887013621, 360597519245983805⟩, ⟨(-918586505682919003), (-917690906573990459)⟩, true⟩

def words08 : List Nat := [360582041398724999, 360582041496658295, 360582041497415975, 360582041373105095, 360582041248663191, 360582041006062567, 360582041091403801, 360582041237512964, 360582041240271734, 360582041502201883]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 59280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 59200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603769589219357, 360603791956005047⟩, ⟨(-1290515105781160513), (-1289619043252415617)⟩, true⟩

def words09 : List Nat := [360582041996820409, 360582042491675098, 360582043069831994, 360582043518464617, 360582043694587655, 360582043870771618, 360582043973474445, 360582044217695946, 360582044585108217, 360582044952695619]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 59290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 59200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 59200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk592B
