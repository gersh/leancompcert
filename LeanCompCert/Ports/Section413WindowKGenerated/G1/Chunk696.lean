import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk696

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485433140605502, 362485504999615199⟩, ⟨(-11617840279193859), (-8240063181338303)⟩, true⟩

def state01 : KState := ⟨⟨362475876388226352, 362475948268471316⟩, ⟨653581719930253012, 656960975113203916⟩, true⟩

def words00 : List Nat := [371285386669039691, 371285386671432812, 371285386533924763, 371285386397757873, 371285386260703892, 371285386187921586, 371285386012302198, 371285386010687324, 371285386008183194, 371285386006944427]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 69600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 69600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492337481364284, 362492409383098955⟩, ⟨(-492336630841309399), (-488955879650982057)⟩, true⟩

def words01 : List Nat := [371285385923801925, 371285385977445221, 371285386206746449, 371285386209128533, 371285386163975816, 371285386076736216, 371285386071603111, 371285386074229270, 371285386170452647, 371285386273984594]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 69610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 69600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482635124576797, 362482707047831130⟩, ⟨183188420883849392, 186570670382637712⟩, true⟩

def words02 : List Nat := [371285386358482512, 371285386360906467, 371285386389319250, 371285386508500418, 371285386682604412, 371285386684988689, 371285386626950209, 371285386570317232, 371285386512755593, 371285386505972487]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 69620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 69600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475813801518387, 362475885746230117⟩, ⟨658258647705623717, 661642391392741809⟩, true⟩

def words03 : List Nat := [371285386619650255, 371285386772815748, 371285386923892246, 371285386926276340, 371285386838338536, 371285386798618612, 371285386901948687, 371285386904331734, 371285386775875128, 371285386642143282]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 69630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 69600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475820346552422, 362475892312625541⟩, ⟨657799687159505803, 661184918562979225⟩, true⟩

def words04 : List Nat := [371285386507351465, 371285386433879003, 371285386273803257, 371285386201579302, 371285386128633015, 371285386022871326, 371285385664183826, 371285385494747739, 371285385324053131, 371285385276280430]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 69640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 69600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362484346922134100, 362484418909906527⟩, ⟨63910089328114065, 67296832195772649⟩, true⟩

def words05 : List Nat := [371285385141785616, 371285385003142081, 371285384927919820, 371285384947474743, 371285385029209567, 371285385111876660, 371285385165157497, 371285385167543483, 371285384996502517, 371285384985591221]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 69650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 69600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473841512337763, 362473913521339700⟩, ⟨795808218883791246, 799196440710364920⟩, true⟩

def words06 : List Nat := [371285385165023342, 371285385167407762, 371285385114545608, 371285385021399390, 371285384927263210, 371285384897247582, 371285384783364814, 371285384753186259, 371285384722241724, 371285384691724520]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 69660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 69600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493594020949081, 362493666051564205⟩, ⟨(-580489057341922810), (-577099329616595488)⟩, true⟩

def words07 : List Nat := [371285384528723057, 371285384417272252, 371285384337761810, 371285384340162412, 371285384190164251, 371285384005623969, 371285383838524978, 371285383841224438, 371285383911503469, 371285384033085472]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 69670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 69600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471119487883516, 362471191539970183⟩, ⟨985596462860909252, 988987686835172722⟩, true⟩

def words08 : List Nat := [371285384154287710, 371285384156672262, 371285384003512929, 371285383983277781, 371285383961930820, 371285383920155787, 371285383603640285, 371285383270111615, 371285382935598757, 371285382782427282]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 69680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 69600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362461690382226777, 362461762455822164⟩, ⟨1642835191850727862, 1646227914871085826⟩, true⟩

def words09 : List Nat := [371285382582161441, 371285382586526075, 371285382588657006, 371285382591042253, 371285382318957447, 371285382095037859, 371285381869805934, 371285381850696292, 371285381556940855, 371285381220741405]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 69690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 69600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 69600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk696
