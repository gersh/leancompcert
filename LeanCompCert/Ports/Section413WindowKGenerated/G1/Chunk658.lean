import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk658

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479923093191517, 362479987038304106⟩, ⟨360507721533719314, 363349575505295954⟩, true⟩

def state01 : KState := ⟨⟨362486919893947404, 362486983859128551⟩, ⟨(-99869525754161209), (-97026351167674413)⟩, true⟩

def words00 : List Nat := [371285509072958947, 371285509082643605, 371285509258616746, 371285509435474127, 371285509559144389, 371285509561397510, 371285509464085700, 371285509405874848, 371285509516263829, 371285509540987699]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 65800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 65800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479235639643188, 362479299625211876⟩, ⟨405907190091575039, 408751706488217233⟩, true⟩

def words01 : List Nat := [371285509565025386, 371285509589798962, 371285509712013828, 371285509751881966, 371285509861383806, 371285509971766262, 371285510069230570, 371285510071473357, 371285509861242898, 371285509769643481]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 65810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 65800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362470059180725659, 362470123186308707⟩, ⟨1009919075391710066, 1012764909233250020⟩, true⟩

def words02 : List Nat := [371285509678432059, 371285509680675048, 371285509376451127, 371285509045905915, 371285508714458783, 371285508451991149, 371285508099548388, 371285507978684521, 371285507857045585, 371285507736046414]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 65820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 65800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495833946174489, 362495897972040713⟩, ⟨(-686966744031611475), (-684119574846442471)⟩, true⟩

def words03 : List Nat := [371285507503870471, 371285507503500807, 371285507688825412, 371285507691068721, 371285507572366925, 371285507386784266, 371285507242886892, 371285507245358959, 371285507331962398, 371285507492326760]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 65830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 65800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487956822412037, 362488020868541486⟩, ⟨(-168297976099899729), (-165449472681278425)⟩, true⟩

def words04 : List Nat := [371285507622484600, 371285507624767248, 371285507730316154, 371285507900284053, 371285508110772421, 371285508159822215, 371285508203228456, 371285508247410155, 371285508345513256, 371285508386230189]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 65840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 65800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk658
