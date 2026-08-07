import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk850

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362464632533080813, 362464741379522029⟩, ⟨1742054475162300987, 1748301539463628379⟩, true⟩

def state01 : KState := ⟨⟨362473016120461138, 362473124993381698⟩, ⟨1029418380396590709, 1035667695570328161⟩, true⟩

def words00 : List Nat := [371285309392988316, 371285309211522065, 371285308969138243, 371285308853808466, 371285308737609663, 371285308600414838, 371285308319023805, 371285308129325534, 371285307937967969, 371285307885930461]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 85000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 85000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362464384785114095, 362464493684878493⟩, ⟨1763256687458848946, 1769508284764588524⟩, true⟩

def words01 : List Nat := [371285307744829052, 371285307602171161, 371285307458340408, 371285307437329087, 371285307345913444, 371285307257496035, 371285307168062799, 371285307063399580, 371285306773423556, 371285306532264574]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 85010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 85000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467329943978914, 362467438870077239⟩, ⟨1512871243249442311, 1519125079603512463⟩, true⟩

def words02 : List Nat := [371285306289470839, 371285306185914305, 371285305966798562, 371285305734728542, 371285305501497361, 371285305300570719, 371285305033846025, 371285304906519666, 371285304778260935, 371285304624276975]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 85020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 85000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486987770012274, 362487096722832866⟩, ⟨(-158747304149627437), (-152491195464149439)⟩, true⟩

def words03 : List Nat := [371285304416174303, 371285304308821301, 371285304199890085, 371285304164022406, 371285304013046587, 371285303840584874, 371285303666895830, 371285303632647641, 371285303549253998, 371285303573699341]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 85030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 85000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475946821305183, 362476055800832211⟩, ⟨780161633785838635, 786420013719025875⟩, true⟩

def words04 : List Nat := [371285303575943485, 371285303572977451, 371285303398050953, 371285303281790131, 371285303164095204, 371285303081990182, 371285302866959738, 371285302652863008, 371285302437541901, 371285302361840078]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 85040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 85000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362463836937208776, 362463945943298081⟩, ⟨1810222039249132408, 1816482678441617846⟩, true⟩

def words05 : List Nat := [371285302255131364, 371285302237011124, 371285302217898252, 371285302199451240, 371285302046967169, 371285301938311364, 371285301828118274, 371285301748130704, 371285301501186319, 371285301253413784]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469199216503545, 362469308249027825⟩, ⟨1354097479498980994, 1360360367382111648⟩, true⟩

def words06 : List Nat := [371285301004358773, 371285300894671850, 371285300714790603, 371285300566467242, 371285300417141376, 371285300247255169, 371285299892244273, 371285299663577224, 371285299433372410, 371285299319527204]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475847726188771, 362475956785701899⟩, ⟨788468827271905642, 794734011231886308⟩, true⟩

def words07 : List Nat := [371285299133801462, 371285298922607283, 371285298710160442, 371285298624465567, 371285298489396952, 371285298377179435, 371285298264019112, 371285298139522346, 371285297912153298, 371285297806050182]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473821355746960, 362473930441576249⟩, ⟨960902612673320655, 967170035748223845⟩, true⟩

def words08 : List Nat := [371285297726507067, 371285297729469261, 371285297616928179, 371285297503307318, 371285297388649797, 371285297246579027, 371285297050033984, 371285296992758553, 371285296934444181, 371285296877535213]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491298240048948, 362491407352603699⟩, ⟨(-526264621113603382), (-519994923834885262)⟩, true⟩

def words09 : List Nat := [371285296750394075, 371285296758394832, 371285296902840482, 371285296905797027, 371285296880485310, 371285296836915907, 371285296858840306, 371285296876820844, 371285296950664319, 371285297025770467]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk850
