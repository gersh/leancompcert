import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk891

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470886066474190, 362471006102209639⟩, ⟨1252862566560289857, 1260083853896313925⟩, true⟩

def state01 : KState := ⟨⟨362476406728216670, 362476526791635272⟩, ⟨760956520863640816, 768180274913366848⟩, true⟩

def words00 : List Nat := [371285148300855592, 371285148271096764, 371285148145589389, 371285147996957717, 371285147847098567, 371285147728065792, 371285147544867281, 371285147488734195, 371285147431603002, 371285147376024380]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 89100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 89100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489192923276574, 362489313014789690⟩, ⟨(-378487045724569915), (-371260788029840291)⟩, true⟩

def words01 : List Nat := [371285147281405501, 371285147252914530, 371285147316355184, 371285147319470382, 371285147286575447, 371285147244474139, 371285147201175749, 371285147188807868, 371285147158605056, 371285147208885023]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 89110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 89100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481162764434647, 362481282883970154⟩, ⟨337184966764496636, 344413721960500280⟩, true⟩

def words02 : List Nat := [371285147251584691, 371285147254712839, 371285147237757974, 371285147294872325, 371285147362776802, 371285147365883956, 371285147266203423, 371285147165886082, 371285147064266367, 371285147056773481]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 89120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 89100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472254584186907, 362472374731699634⟩, ⟨1131207905940787036, 1138439154890985648⟩, true⟩

def words03 : List Nat := [371285147015570155, 371285146993574079, 371285146970574303, 371285146919771054, 371285146721768471, 371285146563791996, 371285146404129486, 371285146371273294, 371285146232908414, 371285146093096213]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 89130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 89100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482920364638111, 362483040539953240⟩, ⟨180427478906844676, 187661206302275390⟩, true⟩

def words04 : List Nat := [371285145951942215, 371285145895840053, 371285145782292633, 371285145775012338, 371285145766778480, 371285145732284446, 371285145573417608, 371285145530315769, 371285145541849994, 371285145545071606]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 89140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 89100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362479392747599258, 362479512951301910⟩, ⟨494978286785698063, 502214545070772843⟩, true⟩

def words05 : List Nat := [371285145523782942, 371285145503540784, 371285145583905401, 371285145643967108, 371285145709439993, 371285145776062278, 371285145842570375, 371285145845678703, 371285145744392044, 371285145685095885]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 89150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 89100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473018518997894, 362473138750386995⟩, ⟨1063355493134857188, 1070594220088818814⟩, true⟩

def words06 : List Nat := [371285145670980509, 371285145674089139, 371285145571433508, 371285145470385216, 371285145368182030, 371285145278347670, 371285145154375574, 371285145091954646, 371285145028443875, 371285144965707045]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 89160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 89100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477680192142497, 362477800451634052⟩, ⟨647640561711745292, 654881794701589394⟩, true⟩

def words07 : List Nat := [371285144833175629, 371285144792541174, 371285144758147767, 371285144761256822, 371285144603934009, 371285144416883457, 371285144228557613, 371285144094045401, 371285143901087194, 371285143822285562]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 89170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 89100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476381643304356, 362476501930864473⟩, ⟨763423498170393601, 770667234458099447⟩, true⟩

def words08 : List Nat := [371285143742291487, 371285143660490773, 371285143473755567, 371285143396314705, 371285143317291391, 371285143277579861, 371285143106884437, 371285142918660836, 371285142729180702, 371285142666759283]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 89180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 89100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476412680287889, 362476532995864307⟩, ⟨760718080449669501, 767964315655581279⟩, true⟩

def words09 : List Nat := [371285142589839869, 371285142611092847, 371285142629430209, 371285142632598856, 371285142569069479, 371285142545428521, 371285142611742502, 371285142614852664, 371285142554265544, 371285142461286455]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 89190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 89100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 89100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk891
