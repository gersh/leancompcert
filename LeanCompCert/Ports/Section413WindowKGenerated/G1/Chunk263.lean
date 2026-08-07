import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk263

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362511545839951915, 362511555318860059⟩, ⟨(-688837653607392542), (-688669118596166350)⟩, true⟩

def state01 : KState := ⟨⟨362485842106056156, 362485851592479597⟩, ⟨(-12891256762918924), (-12722524060341732)⟩, true⟩

def words00 : List Nat := [371285371886790229, 371285371887624015, 371285370672510970, 371285370518793500, 371285370647271219, 371285370648119404, 371285369733814288, 371285368685008165, 371285368029231192, 371285368048560311]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 26300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 26300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362464691909981525, 362464701403941661⟩, ⟨543823505717442389, 543992436746972221⟩, true⟩

def words01 : List Nat := [371285369358606984, 371285370668911094, 371285371692404149, 371285371693238465, 371285371011064012, 371285370666628643, 371285371418463213, 371285371419297460, 371285370593932817, 371285369809593142]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 26310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 26300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477415144048673, 362477424645465995⟩, ⟨209028798471012505, 209197925812446829⟩, true⟩

def words02 : List Nat := [371285369681469734, 371285369713734100, 371285370488838844, 371285371264211640, 371285371905673596, 371285371906508122, 371285370626367445, 371285369944970654, 371285369875358625, 371285369876222260]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 26320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 26300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495048875787442, 362495058384807096⟩, ⟨(-255372221740369048), (-255202894191457282)⟩, true⟩

def words03 : List Nat := [371285369575102521, 371285369156453594, 371285369221224730, 371285369398232584, 371285369696754108, 371285369995582368, 371285370290030935, 371285370290869718, 371285369587497077, 371285369956342290]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 26330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 26300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362460255436896350, 362460264953357396⟩, ⟨661174157789627988, 661343681383669668⟩, true⟩

def words04 : List Nat := [371285370727657387, 371285370728492456, 371285369580674975, 371285368443005998, 371285367305100789, 371285366231475878, 371285364441539909, 371285364091037379, 371285363740272735, 371285363385288466]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 26340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 26300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362503721047589574, 362503730571609367⟩, ⟨(-484414197455955184), (-484244474651328090)⟩, true⟩

def words05 : List Nat := [371285362433392446, 371285362425278198, 371285363388282973, 371285363389118297, 371285362443885736, 371285361122944932, 371285359917775605, 371285359918697227, 371285360142945817, 371285360840770199]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 26350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 26300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362453109466073044, 362453118997649060⟩, ⟨849962204716508632, 850132126741420906⟩, true⟩

def words06 : List Nat := [371285361355179286, 371285361356029514, 371285361161227246, 371285361605784551, 371285362484405086, 371285362485240795, 371285361448366515, 371285359968684075, 371285358488773072, 371285357606930116]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 26360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 26300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362439456121302034, 362439465660395220⟩, ⟨1210207897224908535, 1210378017516296405⟩, true⟩

def words07 : List Nat := [371285356598228943, 371285356812347081, 371285356859009568, 371285356859845523, 371285354992140582, 371285353523186083, 371285352053889679, 371285351528257005, 371285349810399802, 371285348071976581]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 26370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 26300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362452051303678781, 362452060850269291⟩, ⟨877856334261340127, 878026652370452039⟩, true⟩

def words08 : List Nat := [371285346333324145, 371285345219719394, 371285343391175949, 371285342160666793, 371285340929978238, 371285339483506895, 371285336360786313, 371285334672848668, 371285332984611053, 371285332038309096]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 26380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 26300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470270396011856, 362470279950227310⟩, ⟨397017352318896599, 397187871687804605⟩, true⟩

def words09 : List Nat := [371285330778234434, 371285329497052116, 371285328367314201, 371285328368236134, 371285327906567603, 371285327878573336, 371285327850324103, 371285327516691336, 371285325514219053, 371285324945367000]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 26390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 26300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 26300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk263
