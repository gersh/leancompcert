import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk601

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478048170420924, 362478101137078130⟩, ⟨423522502658940319, 425672754720195029⟩, true⟩

def state01 : KState := ⟨⟨362496014634546645, 362496067619424524⟩, ⟨(-656254534330622921), (-654103187112688253)⟩, true⟩

def words00 : List Nat := [371285183921394956, 371285183990064103, 371285184335081202, 371285184680947343, 371285184983607837, 371285184985643427, 371285185227849858, 371285185489296463, 371285185847444535, 371285186030578678]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494961626606992, 362495014630068948⟩, ⟨(-592924996771593131), (-590772532374321509)⟩, true⟩

def words01 : List Nat := [371285186213662259, 371285186397455653, 371285186811532422, 371285187098607683, 371285187400422119, 371285187703020626, 371285187989203942, 371285187991239256, 371285188071744957, 371285188237753879]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490081698627469, 362490134720247488⟩, ⟨(-299510431857867926), (-297356875702973050)⟩, true⟩

def words02 : List Nat := [371285188626498924, 371285188719114877, 371285188752345086, 371285188786215847, 371285188844381401, 371285188846639380, 371285189043290355, 371285189281692655, 371285189484847514, 371285189569232156]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362511108057303810, 362511161097282016⟩, ⟨(-1563909234717730847), (-1561754574590438175)⟩, true⟩

def words03 : List Nat := [371285189899566947, 371285190230923267, 371285190838250781, 371285191113057241, 371285191353928090, 371285191595439343, 371285191855304841, 371285192012426406, 371285192445618037, 371285192879683532]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362503852469631520, 362503905527981035⟩, ⟨(-1127589126546100033), (-1125433361475487735)⟩, true⟩

def words04 : List Nat := [371285193312004877, 371285193376150428, 371285193688843968, 371285194002652172, 371285194351173389, 371285194490775454, 371285194594421087, 371285194698732058, 371285195079081076, 371285195392464162]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490948469355903, 362491001546084044⟩, ⟨(-351323098288763795), (-349166227651441875)⟩, true⟩

def words05 : List Nat := [371285195777588308, 371285196163515587, 371285196547787453, 371285196648209394, 371285196802343564, 371285196957481441, 371285197335590061, 371285197485854857, 371285197583864661, 371285197682656717]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 60150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 60100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362513987339017833, 362514040433962121⟩, ⟨(-1737440761750419178), (-1735282795137513656)⟩, true⟩

def words06 : List Nat := [371285198057290254, 371285198307297383, 371285198729619417, 371285199152744241, 371285199515223343, 371285199551000515, 371285199862849300, 371285200175764690, 371285200764311788, 371285201245729626]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 60160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 60100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362505526800673922, 362505579914175580⟩, ⟨(-1228271828048104332), (-1226112744744024170)⟩, true⟩

def words07 : List Nat := [371285201733114355, 371285202221189608, 371285202909040148, 371285203459927134, 371285204058437801, 371285204657732001, 371285205253532670, 371285205481561992, 371285205821526349, 371285206162580492]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 60170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 60100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362498502530723047, 362498555662355190⟩, ⟨(-805536746719356982), (-803376572226430994)⟩, true⟩

def words08 : List Nat := [371285206642878281, 371285206755607533, 371285206869343178, 371285206983765088, 371285207180340213, 371285207275889104, 371285207623026655, 371285207970963994, 371285208317284722, 371285208541153907]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 60180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 60100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362508529508504006, 362508582658615801⟩, ⟨(-1409124756214095781), (-1406963469345213181)⟩, true⟩

def words09 : List Nat := [371285208959081121, 371285209378123118, 371285209908707479, 371285210071880749, 371285210192301204, 371285210313333919, 371285210606750284, 371285210780442072, 371285211170062582, 371285211560638273]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 60190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 60100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 60100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk601
