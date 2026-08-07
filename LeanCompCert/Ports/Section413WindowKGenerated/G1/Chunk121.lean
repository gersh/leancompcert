import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk121

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362407105158400912, 362407107033411865⟩, ⟨937003202183729261, 937018555902162635⟩, true⟩

def state01 : KState := ⟨⟨362469616472206569, 362469618350433207⟩, ⟨180314286353001535, 180329678997916207⟩, true⟩

def words00 : List Nat := [371284540581193945, 371284540581589239, 371284537561107607, 371284535598598954, 371284533636301979, 371284530588433849, 371284518480662696, 371284513164551943, 371284509322722207, 371284509323100253]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 12100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 12100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491365570685080, 362491367452188104⟩, ⟨(-83139655916142108), (-83124223577306062)⟩, true⟩

def words01 : List Nat := [371284508093830111, 371284505414813989, 371284506842798947, 371284507585002085, 371284510440540311, 371284513295742494, 371284514666196508, 371284514666556188, 371284509017452051, 371284509583730279]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 12110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 12100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362472894935527467, 362472896820239218⟩, ⟨140952709722624203, 140968180967830057⟩, true⟩

def words02 : List Nat := [371284512370258473, 371284512370621629, 371284511419117591, 371284510512149723, 371284510110222673, 371284510110619115, 371284511433572811, 371284514894172320, 371284518269245711, 371284518269618265]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 12120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 12100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362536512178839056, 362536514066806186⟩, ⟨(-631264229665851799), (-631248718916128961)⟩, true⟩

def words03 : List Nat := [371284519190173478, 371284521068595963, 371284526469073834, 371284526469434061, 371284522848048899, 371284518049115528, 371284513866444574, 371284513866848918, 371284516643100882, 371284520926297486]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 12130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 12100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490197996280366, 362490199887503637⟩, ⟨(-68976074102034163), (-68960523806427061)⟩, true⟩

def words04 : List Nat := [371284524889285447, 371284524889647535, 371284526822117932, 371284531163698243, 371284535596246922, 371284535596607456, 371284531024953394, 371284526475743461, 371284524123812188, 371284524591329954]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 12140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 12100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362404946728445968, 362404948622926330⟩, ⟨967614498857071496, 967630088742603694⟩, true⟩

def words05 : List Nat := [371284529913785837, 371284535235521447, 371284540581114683, 371284540581475455, 371284538137496327, 371284534983865780, 371284535412633199, 371284535412994081, 371284530009861732, 371284523465750558]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 12150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 12100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362545590477912568, 362545592375625272⟩, ⟨(-743033178857508391), (-743017549650106377)⟩, true⟩

def words06 : List Nat := [371284517111202409, 371284517111599675, 371284517453004564, 371284520988891135, 371284523362486147, 371284523362855802, 371284526065424437, 371284529849135467, 371284539166570374, 371284544183229405]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 12160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 12100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474073174238219, 362474075075244378⟩, ⟨127819560709576305, 127835230014932623⟩, true⟩

def words07 : List Nat := [371284549223128601, 371284554262318614, 371284560718276972, 371284563796552702, 371284568867787444, 371284573938330986, 371284577167528853, 371284577167890333, 371284571439849751, 371284570578529677]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 12170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 12100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362386910063847634, 362386911968074658⟩, ⟨1189998014133269003, 1190013722685678059⟩, true⟩

def words08 : List Nat := [371284573205928532, 371284573206290283, 371284567745353874, 371284562281104101, 371284556817610486, 371284553432189889, 371284546732716362, 371284542847074683, 371284538961950706, 371284534094628037]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 12180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 12100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362562203464929869, 362562205372434479⟩, ⟨(-947582177624595696), (-947566429101990242)⟩, true⟩

def words09 : List Nat := [371284526087153388, 371284523754730290, 371284524631662064, 371284524632032142, 371284524263159377, 371284522870924248, 371284526773825926, 371284529625477019, 371284535992589642, 371284542358820678]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 12190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 12100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 12100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk121
