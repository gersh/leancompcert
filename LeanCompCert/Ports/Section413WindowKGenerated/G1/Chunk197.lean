import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk197

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362526447027582777, 362526452216650171⟩, ⟨(-809024127361852915), (-808954989186496073)⟩, true⟩

def state01 : KState := ⟨⟨362449569259404503, 362449574453979570⟩, ⟨705567244630554422, 705636491335593498⟩, true⟩

def words00 : List Nat := [371285392295288818, 371285392295899370, 371285390569733888, 371285389709703850, 371285388849462972, 371285388030119420, 371285384221982274, 371285380424330523, 371285376626819168, 371285375392149819]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 19700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 19700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362407559843318139, 362407565043405307⟩, ⟨1533998056831944965, 1534067412207752741⟩, true⟩

def words01 : List Nat := [371285373579041561, 371285373582496794, 371285373596386119, 371285373596996995, 371285370189725785, 371285367580538814, 371285364971307525, 371285364922051280, 371285361452885191, 371285357508527404]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 19710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 19700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362441567229776647, 362441572435334286⟩, ⟨863178859121845590, 863248322403298750⟩, true⟩

def words02 : List Nat := [371285353564293634, 371285350454022774, 371285346418648462, 371285343525910867, 371285340633282767, 371285337320731786, 371285331874253184, 371285328985922519, 371285326097554769, 371285325518071403]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 19720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 19700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362451589089087762, 362451594300216989⟩, ⟨665421375767576771, 665490949004375097⟩, true⟩

def words03 : List Nat := [371285323301049420, 371285321096712284, 371285318892363451, 371285317776721046, 371285316100021100, 371285315220775784, 371285314341414409, 371285313083303922, 371285308821416213, 371285307114249633]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 19730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 19700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362373122301964699, 362373127518541643⟩, ⟨2214872213281612155, 2214941894084870719⟩, true⟩

def words04 : List Nat := [371285305590031374, 371285305590643481, 371285302363001664, 371285299148827530, 371285295934739730, 371285292768293850, 371285288335243910, 371285284490604698, 371285280646154617, 371285276475204169]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 19740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 19700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499725846350108, 362499731068468596⟩, ⟨(-286113855348701402), (-286044065072340874)⟩, true⟩

def words05 : List Nat := [371285270797479238, 371285267671520829, 371285264545557922, 371285263970733845, 371285261865915547, 371285259384733146, 371285256903555394, 371285256236874229, 371285255153544181, 371285255886793968]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 19750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 19700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362439091094361513, 362439096322008906⟩, ⟨912199684364812097, 912269583920953283⟩, true⟩

def words06 : List Nat := [371285256067009014, 371285256067622006, 371285253323903840, 371285253129155393, 371285253067178345, 371285253067791187, 371285249797463902, 371285245972034361, 371285242146726745, 371285240458777796]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 19760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 19700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362424056593357879, 362424061826518220⟩, ⟨1209569076620940536, 1209639085195971206⟩, true⟩

def words07 : List Nat := [371285238125264914, 371285237407634614, 371285236689882419, 371285235950346710, 371285231809849064, 371285227859275312, 371285223908776059, 371285222503342276, 371285219573202773, 371285216481988189]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 19770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 19700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362450617860645871, 362450623099301374⟩, ⟨684370114726191212, 684440232023805850⟩, true⟩

def words08 : List Nat := [371285213390819118, 371285212482162071, 371285211072055580, 371285211486807781, 371285211487282433, 371285211474318627, 371285209041348911, 371285208708441722, 371285208375266379, 371285208255037797]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 19780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 19700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362464862679047955, 362464867923307177⟩, ⟨402491685037955920, 402561913260529984⟩, true⟩

def words09 : List Nat := [371285206507981979, 371285204762455876, 371285203811558501, 371285203812234324, 371285203332370978, 371285203238214785, 371285203143855374, 371285203060201828, 371285200359181245, 371285199333067810]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 19790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 19700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 19700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk197
