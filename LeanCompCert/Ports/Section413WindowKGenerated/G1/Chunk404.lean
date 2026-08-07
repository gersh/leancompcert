import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk404

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489495335897179, 362489518515038971⟩, ⟨(-173545285463535956), (-172912508124931230)⟩, true⟩

def state01 : KState := ⟨⟨362454622805622706, 362454645996727424⟩, ⟨1235396595581047416, 1236029856282714170⟩, true⟩

def words00 : List Nat := [371285238671265329, 371285238672590710, 371285237919447024, 371285237480815021, 371285237041529808, 371285236787175387, 371285235799805364, 371285234812760480, 371285233825216654, 371285233224054391]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 40400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 40400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362437970347498257, 362437993550542682⟩, ⟨1908435032243332844, 1909068775489321420⟩, true⟩

def words01 : List Nat := [371285232468067482, 371285231857441766, 371285231246413213, 371285230618324675, 371285229468776758, 371285228406395472, 371285227343366196, 371285226682446786, 371285225513623567, 371285224346571612]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 40410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 40400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483671975283102, 362483695190189714⟩, ⟨60973254017750439, 61607476793486907⟩, true⟩

def words02 : List Nat := [371285223178999864, 371285222564756332, 371285221644183557, 371285221335728592, 371285221026889782, 371285220492113818, 371285219506387912, 371285219132808871, 371285218994815594, 371285218996194995]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 40420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 40400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480788170115465, 362480811397128858⟩, ⟨177686077475820010, 178320789789715576⟩, true⟩

def words03 : List Nat := [371285218959497572, 371285218922990185, 371285219459164635, 371285219787014671, 371285220298608030, 371285220810681114, 371285221321753376, 371285221323080130, 371285221019594762, 371285220912207734]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 40430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 40400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362462548584164281, 362462571823000173⟩, ⟨915441402288589175, 916076592765216425⟩, true⟩

def words04 : List Nat := [371285221173515744, 371285221174842793, 371285220835379595, 371285220429823717, 371285220023792420, 371285219802721656, 371285219368178072, 371285219247865496, 371285219127092311, 371285218957555556]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 40440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 40400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492483426659041, 362492506677493158⟩, ⟨(-295618404760931754), (-294982728894943230)⟩, true⟩

def words05 : List Nat := [371285218398592265, 371285218286310102, 371285218311148791, 371285218312476123, 371285217728326638, 371285217072625251, 371285216416399825, 371285216200144811, 371285215951099324, 371285216132798392]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 40450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 40400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362450175314790832, 362450198577594318⟩, ⟨1416359298864473894, 1416995459072329984⟩, true⟩

def words06 : List Nat := [371285216313805047, 371285216315132533, 371285215682644228, 371285215548063218, 371285215461141123, 371285215462468682, 371285214698618818, 371285213756661355, 371285212814233318, 371285212055703346]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 40460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 40400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362449561678379302, 362449584953147666⟩, ⟨1441333292670459680, 1441969937157103324⟩, true⟩

def words07 : List Nat := [371285211191454840, 371285210937695305, 371285210683498976, 371285210427887079, 371285209700164811, 371285209163209361, 371285208625610505, 371285208474123537, 371285207618616551, 371285206740132773]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 40470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 40400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471043398530372, 362471066685196513⟩, ⟨571693826103537354, 572330952273003560⟩, true⟩

def words08 : List Nat := [371285205861086689, 371285205234306022, 371285204389864370, 371285204155543966, 371285203920832801, 371285203590961011, 371285202575319455, 371285202169952989, 371285201802425434, 371285201803800440]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 40480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 40400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471875535361685, 362471898834121805⟩, ⟨538015691830519618, 538653307745530638⟩, true⟩

def words09 : List Nat := [371285201455716863, 371285200986486884, 371285200655474980, 371285200656942429, 371285200552045366, 371285200428005327, 371285200303506069, 371285200179209618, 371285199242551222, 371285198915794535]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 40490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 40400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 40400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk404
