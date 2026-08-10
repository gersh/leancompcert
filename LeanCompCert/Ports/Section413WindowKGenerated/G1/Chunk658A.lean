import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk658A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk658A
