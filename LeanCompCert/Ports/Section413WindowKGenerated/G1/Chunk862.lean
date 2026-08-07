import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk862

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470100108411152, 362470212171131731⟩, ⟨1287549372503639850, 1294071755428587992⟩, true⟩

def state01 : KState := ⟨⟨362470543975189289, 362470656064736328⟩, ⟨1249318329591319535, 1255843025094508543⟩, true⟩

def words00 : List Nat := [371285224432365899, 371285224395957479, 371285224291024589, 371285224246730684, 371285224201567164, 371285224122099448, 371285223862379911, 371285223637296044, 371285223410617725, 371285223319406257]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 86200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 86200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362470760035517527, 362470872152399036⟩, ⟨1230719151096071905, 1237246203244148791⟩, true⟩

def words01 : List Nat := [371285223152700043, 371285222986654003, 371285222819362335, 371285222774831445, 371285222661875013, 371285222580348464, 371285222497770422, 371285222404613763, 371285222189895369, 371285222027175703]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 86210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 86200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362464568395573367, 362464680539165185⟩, ⟨1764630519688964241, 1771159874938898375⟩, true⟩

def words02 : List Nat := [371285221862777698, 371285221817606826, 371285221632399450, 371285221436717111, 371285221239844426, 371285221083817337, 371285220877222123, 371285220758246691, 371285220638336006, 371285220489007919]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 86220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 86200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362476699173669400, 362476811344431142⟩, ⟨718510864218981449, 725042562464392609⟩, true⟩

def words03 : List Nat := [371285220252845124, 371285220135067768, 371285220015746844, 371285219931305085, 371285219666989188, 371285219381862782, 371285219095549461, 371285218933519034, 371285218703756647, 371285218609765841]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 86230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 86200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473501138307274, 362473613336087827⟩, ⟨994297508175952493, 1000831536662436231⟩, true⟩

def words04 : List Nat := [371285218514532928, 371285218398354677, 371285218178553441, 371285218094569789, 371285218009137723, 371285217954882026, 371285217753588570, 371285217517990687, 371285217281150439, 371285217179991160]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 86240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 86200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362474927983236696, 362475040208004088⟩, ⟨871243808708956963, 877780164948354923⟩, true⟩

def words05 : List Nat := [371285217047503277, 371285216985258872, 371285216922029882, 371285216859725835, 371285216696878107, 371285216560588153, 371285216422670938, 371285216419984673, 371285216304133528, 371285216189512880]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484819700631444, 362484931952274933⟩, ⟨17947295418454656, 24485970125702882⟩, true⟩

def words06 : List Nat := [371285216073615459, 371285216014533266, 371285215932063025, 371285215960209504, 371285215965438823, 371285215968439008, 371285215794287178, 371285215746087748, 371285215778658974, 371285215781765205]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473024690452848, 362473136969439622⟩, ⟨1035569246183917523, 1042110279934621753⟩, true⟩

def words07 : List Nat := [371285215780717769, 371285215776401834, 371285215798746560, 371285215802084227, 371285215764988757, 371285215701501891, 371285215637029923, 371285215573448616, 371285215342587282, 371285215206341971]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471134689213064, 362471246994949878⟩, ⟨1198677007721028384, 1205220349604944706⟩, true⟩

def words08 : List Nat := [371285215068399204, 371285215020669158, 371285214860712206, 371285214701850085, 371285214541844372, 371285214424193845, 371285214246140822, 371285214203506542, 371285214159859679, 371285214086728821]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497489736128507, 362497602068974624⟩, ⟨(-1075627897885620949), (-1069082216606744961)⟩, true⟩

def words09 : List Nat := [371285213926903352, 371285213902798946, 371285213983555964, 371285213986571523, 371285213966931602, 371285213908470988, 371285213921029285, 371285213945344448, 371285214090926805, 371285214237818476]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk862
