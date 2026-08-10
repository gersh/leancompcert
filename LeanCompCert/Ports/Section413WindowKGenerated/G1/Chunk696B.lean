import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk696A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk696B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk696A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk696B
