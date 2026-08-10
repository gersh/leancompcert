import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk838A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk838B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk838A

def state06 : KState := ⟨⟨362482890268521476, 362482996104679963⟩, ⟨189719852550964434, 195712754220770200⟩, true⟩

def words05 : List Nat := [371285329572003699, 371285329761965335, 371285329902779252, 371285329905688758, 371285329856772373, 371285329843938963, 371285329955351405, 371285329958265247, 371285329932624965, 371285329908093042]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 83850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 83800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487353364863072, 362487459227043956⟩, ⟨(-184559002363700618), (-178563918320241522)⟩, true⟩

def words06 : List Nat := [371285329943712365, 371285329946952105, 371285330025328212, 371285330113978268, 371285330178627699, 371285330181543901, 371285330098714773, 371285330076129487, 371285330168131462, 371285330196528996]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 83860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 83800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491797211185913, 362491903099940344⟩, ⟨(-557269825815698423), (-551272512914899035)⟩, true⟩

def words07 : List Nat := [371285330223971721, 371285330252417735, 371285330421734501, 371285330540718427, 371285330655709302, 371285330771784514, 371285330887709230, 371285330890627597, 371285330939467394, 371285331021484974]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 83870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 83800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480720713259397, 362480826627975546⟩, ⟨371866285481630344, 377865776184325546⟩, true⟩

def words08 : List Nat := [371285331137780122, 371285331140690638, 371285331067747811, 371285330995737960, 371285330922644852, 371285330882847768, 371285330842748278, 371285330886404801, 371285330925548275, 371285330928561842]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 83880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 83800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491086801861709, 362491192742825805⟩, ⟨(-497779566167056965), (-491777873388995651)⟩, true⟩

def words09 : List Nat := [371285330965192911, 371285331056992385, 371285331264497371, 371285331283590549, 371285331285889492, 371285331258426433, 371285331240350470, 371285331243589945, 371285331263137569, 371285331336246754]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 83890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 83800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 83800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk838B
