import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk924

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489360366636136, 362489489821714334⟩, ⟨(-413188157756967330), (-405111961464603156)⟩, true⟩

def state01 : KState := ⟨⟨362481892538909374, 362482022022697652⟩, ⟨276913827746896797, 284992677005241799⟩, true⟩

def words00 : List Nat := [371285105707307612, 371285105740799739, 371285105773965342, 371285105808186563, 371285105877073799, 371285105888871131, 371285105932816084, 371285105978065416, 371285106021916962, 371285106025262367]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 92400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 92400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501281028205991, 362501410541185318⟩, ⟨(-1514886612611552182), (-1506805065663547702)⟩, true⟩

def words01 : List Nat := [371285106008885577, 371285106027552268, 371285106161600530, 371285106225679991, 371285106261207341, 371285106297794173, 371285106410905566, 371285106473829653, 371285106652433713, 371285106832443111]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 92410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 92400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492594667705973, 362492724209910174⟩, ⟨(-712080567163789363), (-703996319103021527)⟩, true⟩

def words02 : List Nat := [371285106983358301, 371285107030240971, 371285107163026287, 371285107297512172, 371285107465764694, 371285107499307700, 371285107531769054, 371285107565353083, 371285107671288280, 371285107757430995]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 92420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 92400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482214290309352, 362482343861595028⟩, ⟨247480784558140875, 255567720772026815⟩, true⟩

def words03 : List Nat := [371285107959043624, 371285108162011442, 371285108342804287, 371285108383436355, 371285108427140211, 371285108472362599, 371285108600138084, 371285108603370409, 371285108575431417, 371285108549184514]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 92430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 92400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489595436218283, 362489725036504858⟩, ⟨(-434825631310147305), (-426736014111572073)⟩, true⟩

def words04 : List Nat := [371285108588887265, 371285108623379516, 371285108730093869, 371285108838106125, 371285108926566385, 371285108929807956, 371285108975717322, 371285109057138985, 371285109175779940, 371285109229059708]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 92440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 92400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489742056648596, 362489871686340383⟩, ⟨(-448370874678222765), (-440278538820735571)⟩, true⟩

def words05 : List Nat := [371285109281131053, 371285109334267262, 371285109481869185, 371285109585027572, 371285109677270771, 371285109770842281, 371285109863724451, 371285109866957531, 371285109855208673, 371285109910685559]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 92450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 92400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489423188639893, 362489552847174512⟩, ⟨(-418887723345274867), (-410792720528416269)⟩, true⟩

def words06 : List Nat := [371285110081318976, 371285110110882404, 371285110113349965, 371285110102619343, 371285110112173142, 371285110115794629, 371285110198521729, 371285110300730998, 371285110400591936, 371285110452039514]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 92460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 92400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495660581907984, 362495790269673718⟩, ⟨(-995686264751366169), (-987588558787165041)⟩, true⟩

def words07 : List Nat := [371285110606041784, 371285110761747151, 371285110984648835, 371285111052745336, 371285111098420636, 371285111145044597, 371285111204151075, 371285111207715096, 371285111323953928, 371285111443117051]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 92470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 92400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489494475712239, 362489624192649939⟩, ⟨(-425451077940102130), (-417350674002184322)⟩, true⟩

def words08 : List Nat := [371285111553439883, 371285111556689387, 371285111634669490, 371285111718578767, 371285111826538533, 371285111829772785, 371285111794190323, 371285111759461372, 371285111801955806, 371285111854433225]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 92480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 92400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477092930347538, 362477222676415436⟩, ⟨721648869221810457, 729751967558040473⟩, true⟩

def words09 : List Nat := [371285111946405825, 371285112039632971, 371285112125057921, 371285112128292577, 371285112069899129, 371285112033035064, 371285112027258160, 371285112030549234, 371285111968555092, 371285111886875523]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 92490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 92400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 92400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk924
