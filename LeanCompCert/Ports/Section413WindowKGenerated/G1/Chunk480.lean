import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk480

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477583074545385, 362477616256642734⟩, ⟨364434100040081794, 365510189046594040⟩, true⟩

def state01 : KState := ⟨⟨362468052567597541, 362468085763924460⟩, ⟨821961320441177579, 823038092541303735⟩, true⟩

def words00 : List Nat := [371285231044966335, 371285231046563782, 371285230620216673, 371285230195780765, 371285229770754793, 371285229479975245, 371285229041335915, 371285228969790258, 371285228897696136, 371285228819382517]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 48000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 48000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482866055583297, 362482899266344275⟩, ⟨110654991415296536, 111732456568472788⟩, true⟩

def words01 : List Nat := [371285228463402216, 371285228438243985, 371285228505387589, 371285228506985363, 371285228023843544, 371285227375915185, 371285226727344257, 371285226512045840, 371285226103005241, 371285226056360279]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 48010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 48000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482368066977639, 362482401292151369⟩, ⟨134518657132944207, 135596814459402991⟩, true⟩

def words02 : List Nat := [371285226009101667, 371285225963659789, 371285225503416137, 371285225476504986, 371285225465256987, 371285225466867030, 371285225173732449, 371285224792297388, 371285224459482661, 371285224461305219]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 48020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 48000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362469906422634723, 362469939662208308⟩, ⟨733239509080487819, 734318358105764581⟩, true⟩

def words03 : List Nat := [371285224708125188, 371285225014385438, 371285225308058503, 371285225323842134, 371285225417259035, 371285225511438225, 371285225813212544, 371285225814811243, 371285225539748973, 371285225223367879]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 48030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 48000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482025389401239, 362482058643323104⟩, ⟨151002656078969959, 152082194464954911⟩, true⟩

def words04 : List Nat := [371285224906294457, 371285224771643646, 371285224542082106, 371285224624629671, 371285224633977097, 371285224635575992, 371285224068043008, 371285223810251766, 371285223723755806, 371285223725413946]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 48040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 48000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362464383976929153, 362464417245394073⟩, ⟨998843722589176123, 999923959843249187⟩, true⟩

def words05 : List Nat := [371285223660754221, 371285223585536108, 371285223758194496, 371285223791436320, 371285223838765006, 371285223886697571, 371285223939983780, 371285223941582965, 371285223418318969, 371285222987379992]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 48050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 48000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362464483139470464, 362464516422201934⟩, ⟨994089507282942620, 995170430260691580⟩, true⟩

def words06 : List Nat := [371285222555567844, 371285222411433242, 371285221906931272, 371285221360897239, 371285220814252011, 371285220401445821, 371285219771140242, 371285219524229259, 371285219276836245, 371285218948315117]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 48060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 48000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362511125173811758, 362511158471015363⟩, ⟨(-1248221465464788238), (-1247139846737795942)⟩, true⟩

def words07 : List Nat := [371285218518735672, 371285218457449109, 371285218763645327, 371285218770048541, 371285218771288414, 371285218709777905, 371285218970015395, 371285219079880924, 371285219620471625, 371285220161771841]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 48070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 48000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479405910456809, 362479439222104185⟩, ⟨276925961580246416, 278008274839244640⟩, true⟩

def words08 : List Nat := [371285220634607055, 371285220638828135, 371285220823927529, 371285221009810749, 371285221256457004, 371285221258057288, 371285220929028958, 371285220587645961, 371285220245615654, 371285220221788928]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 48080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 48000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362457624964743662, 362457658290792331⟩, ⟨1324593202341999418, 1325676208231346064⟩, true⟩

def words09 : List Nat := [371285220413662857, 371285220726380547, 371285220936545097, 371285220938145964, 371285220625951528, 371285220447611150, 371285220269500059, 371285220271100939, 371285219697930577, 371285219126722297]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 48090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 48000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 48000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk480
