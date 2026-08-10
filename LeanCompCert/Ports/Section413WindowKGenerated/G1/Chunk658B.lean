import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk658A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk658B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk658A

def state06 : KState := ⟨⟨362488040318434930, 362488104384761504⟩, ⟨(-173732226525743055), (-170882393027399687)⟩, true⟩

def words05 : List Nat := [371285508656411114, 371285508927476484, 371285509196416661, 371285509228162870, 371285509329667311, 371285509432359268, 371285509652288409, 371285509710254588, 371285509751330614, 371285509793227404]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362498104810538232, 362498168896957462⟩, ⟨(-836628619833738558), (-833777462927902446)⟩, true⟩

def words06 : List Nat := [371285510028141735, 371285510149276832, 371285510338190300, 371285510528004232, 371285510680503514, 371285510682747924, 371285510601954190, 371285510678668425, 371285510970456199, 371285511164982422]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485251436356472, 362485315543262196⟩, ⟨10140067105622999, 12992573556257385⟩, true⟩

def words07 : List Nat := [371285511352136659, 371285511540052152, 371285511894889947, 371285512135528169, 371285512390399220, 371285512646095326, 371285512855101887, 371285512857346779, 371285512759174838, 371285512759011381]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483749697446457, 362483813824347071⟩, ⟨109093566323667120, 111947390141630062⟩, true⟩

def words08 : List Nat := [371285512984835349, 371285512987080332, 371285512909076551, 371285512831785971, 371285512753604625, 371285512746734714, 371285512697243115, 371285512762434404, 371285512826258829, 371285512828598728]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499592301824450, 362499656449016595⟩, ⟨(-934877817718727676), (-932022656788699714)⟩, true⟩

def words09 : List Nat := [371285512874272019, 371285512946853699, 371285513228016729, 371285513247740582, 371285513249480855, 371285513220536196, 371285513259179847, 371285513261720983, 371285513462342606, 371285513679456366]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk658B
