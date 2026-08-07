import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk173

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362531512576929908, 362531516532958755⟩, ⟨(-793139836476962889), (-793093544114076909)⟩, true⟩

def state01 : KState := ⟨⟨362470449190589190, 362470453151402335⟩, ⟨263372985882837136, 263419361038780524⟩, true⟩

def words00 : List Nat := [371285678353957241, 371285678354488111, 371285677312710085, 371285677285972461, 371285678217005206, 371285678217537341, 371285675804710229, 371285673368066006, 371285670931493975, 371285670907672629]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 17300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 17300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362463116005200464, 362463119970806006⟩, ⟨390436127753719281, 390482585890377199⟩, true⟩

def words01 : List Nat := [371285670535247463, 371285671042059966, 371285671439760974, 371285671440295550, 371285668873663608, 371285667294721745, 371285667467782455, 371285667468322694, 371285666455908384, 371285665154748869]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 17310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 17300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478193007932353, 362478196978290867⟩, ⟨129477902447768353, 129524442930020107⟩, true⟩

def words02 : List Nat := [371285665882698217, 371285666252227001, 371285668688808669, 371285671125318665, 371285672329736489, 371285672330267887, 371285669204532903, 371285669306456942, 371285670979064107, 371285670979614008]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 17320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 17300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472012263647539, 362472016238845544⟩, ⟨236842127473005418, 236888751848370318⟩, true⟩

def words03 : List Nat := [371285670548761215, 371285670092267988, 371285672505858800, 371285673795163074, 371285676067740255, 371285678340266398, 371285680598061092, 371285680598592805, 371285678430467356, 371285677643219730]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 17330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 17300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362464443167518770, 362464447147454554⟩, ⟨368403698541877116, 368450405094695992⟩, true⟩

def words04 : List Nat := [371285679391389722, 371285679848083924, 371285679903819271, 371285679959730601, 371285681000441910, 371285681001037562, 371285681730567629, 371285682612155771, 371285683481491113, 371285683482042145]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 17340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 17300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362522800047595881, 362522804032353889⟩, ⟨(-644446667627229601), (-644399877384772827)⟩, true⟩

def words05 : List Nat := [371285684354087351, 371285686450100879, 371285689173493239, 371285689174025314, 371285687479359439, 371285685384973309, 371285683290618919, 371285683262214903, 371285684223133918, 371285686361863435]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 17350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 17300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362442321320850495, 362442325310410030⟩, ⟨752965117648847416, 753011991270981192⟩, true⟩

def words06 : List Nat := [371285688493898349, 371285688494430748, 371285686584325376, 371285686956646654, 371285687647104846, 371285687647638518, 371285684962346764, 371285681614730123, 371285678267278575, 371285676605244284]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 17360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 17300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362446506031640493, 362446510025990484⟩, ⟨680501537852798963, 680548494709603201⟩, true⟩

def words07 : List Nat := [371285674109993498, 371285673985173030, 371285673860192394, 371285673724921450, 371285671659448646, 371285670508935846, 371285671515880141, 371285671516413057, 371285669269004272, 371285667016480105]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 17370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 17300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491769513240767, 362491773512366000⟩, ⟨(-106453438113514386), (-106406398239417680)⟩, true⟩

def words08 : List Nat := [371285664763988452, 371285663286257527, 371285660338584523, 371285660518728994, 371285660519142559, 371285660229059467, 371285655537411921, 371285654151813813, 371285654685002944, 371285655037393922]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 17380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 17300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487125523785943, 362487129527772553⟩, ⟨(-25596938391842179), (-25549813954031243)⟩, true⟩

def words09 : List Nat := [371285655037796964, 371285654591609527, 371285657001843720, 371285658634963332, 371285660342714423, 371285662050461212, 371285663754361083, 371285663754894818, 371285661146994875, 371285661232045065]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 17390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 17300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 17300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk173
