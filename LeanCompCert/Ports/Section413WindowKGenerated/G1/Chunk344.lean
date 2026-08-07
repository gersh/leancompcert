import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk344

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362512070680065835, 362512087265316917⟩, ⟨(-939543561397372778), (-939157964712828750)⟩, true⟩

def state01 : KState := ⟨⟨362483633923651627, 362483650518949277⟩, ⟨38763295078693184, 39149237416177090⟩, true⟩

def words00 : List Nat := [371284787747442001, 371284787748557224, 371284788163041323, 371284788793620228, 371284789459185016, 371284789460300353, 371284789000255937, 371284788542530545, 371284788246168491, 371284788247441465]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 34400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 34400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362448099638210301, 362448116243555207⟩, ⟨1261822718822224188, 1262209006938112126⟩, true⟩

def words01 : List Nat := [371284788732130004, 371284789250311420, 371284789765778679, 371284789766894464, 371284789157275536, 371284788807186985, 371284788844524566, 371284788845640426, 371284788109797011, 371284787045616164]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 34410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 34400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362497751403081020, 362497768018412201⟩, ⟨(-447414444846820697), (-447027812952035245)⟩, true⟩

def words02 : List Nat := [371284785981012390, 371284785760665086, 371284785119790713, 371284785108152007, 371284785096163733, 371284784864597839, 371284783935855591, 371284783791965736, 371284784345655933, 371284784723911547]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 34420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 34400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492388867774500, 362492405493296039⟩, ⟨(-262768264128601203), (-262381281329541055)⟩, true⟩

def words03 : List Nat := [371284785042555404, 371284785361571779, 371284786024139005, 371284786265182904, 371284786640851686, 371284787016915251, 371284787386472712, 371284787387589549, 371284786987776274, 371284787210396892]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 34430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 34400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362457535645274676, 362457552280737293⟩, ⟨937763883256766255, 938151208478247635⟩, true⟩

def words04 : List Nat := [371284787718515766, 371284787719635545, 371284787372344753, 371284786977630554, 371284786582522323, 371284786431404532, 371284785860489671, 371284785420035424, 371284784979215818, 371284784536426067]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 34440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 34400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362516747221926010, 362516763867470064⟩, ⟨(-1102329258399001434), (-1101941585821393612)⟩, true⟩

def words05 : List Nat := [371284783746721065, 371284783660847200, 371284784228934043, 371284784344014648, 371284784344879145, 371284784324410180, 371284785123897265, 371284785526401185, 371284786455145976, 371284787384320377]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 34450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 34400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479006658609415, 362479023314255838⟩, ⟨198224417707973385, 198612438465317329⟩, true⟩

def words06 : List Nat := [371284788127147316, 371284788128264679, 371284787749122091, 371284787612932844, 371284787548145787, 371284787549265672, 371284786754710858, 371284785958321848, 371284785205586095, 371284785206871601]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 34460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 34400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362465955424609788, 362465972090324620⟩, ⟨648331087648168640, 648719455514729232⟩, true⟩

def words07 : List Nat := [371284785714878289, 371284786390462281, 371284787063364996, 371284787064490201, 371284786988185762, 371284786973777029, 371284787540895634, 371284787542013398, 371284787004090435, 371284786459684096]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 34470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 34400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477675163180397, 362477691838911610⟩, ⟨244303462393893418, 244692175676814102⟩, true⟩

def words08 : List Nat := [371284785914799312, 371284785827658401, 371284785872733971, 371284786316530507, 371284786564025215, 371284786565143659, 371284785968018981, 371284786090841523, 371284786420986573, 371284786422143759]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 34480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 34400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486335443309857, 362486352129213913⟩, ⟨(-54429041255787079), (-54039977061178941)⟩, true⟩

def words09 : List Nat := [371284786217286090, 371284786010676645, 371284786122192135, 371284786123423652, 371284786181547070, 371284786340089407, 371284786499300410, 371284786500419131, 371284785751692561, 371284785798468104]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 34490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 34400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 34400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk344
