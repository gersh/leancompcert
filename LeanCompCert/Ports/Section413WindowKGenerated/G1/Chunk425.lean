import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk425

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362525739797166654, 362525765554182937⟩, ⟨(-1725150252605198555), (-1724410597415655113)⟩, true⟩

def state01 : KState := ⟨⟨362514649885086136, 362514675654737076⟩, ⟨(-1253868261548238183), (-1253128069323329877)⟩, true⟩

def words00 : List Nat := [371285193111642272, 371285193426926722, 371285194142049472, 371285194857916220, 371285195737826219, 371285195970975448, 371285196203453343, 371285196436370443, 371285197222896749, 371285197917931936]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 42500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 42500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486173106334953, 362486198888621219⟩, ⟨(-43126742606942981), (-42386013188393345)⟩, true⟩

def words01 : List Nat := [371285198840231795, 371285199763059212, 371285200630752416, 371285200905070708, 371285201203136492, 371285201501873204, 371285201986747830, 371285202013690661, 371285202038183077, 371285202063212871]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 42510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 42500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362504101534018106, 362504127328843644⟩, ⟨(-805463236600987826), (-804721973948364252)⟩, true⟩

def words02 : List Nat := [371285202550105524, 371285202825151590, 371285203459118065, 371285204093606938, 371285204590818040, 371285204593753290, 371285204922922929, 371285205252820461, 371285206048908457, 371285206495241134]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 42520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 42500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362494056978247813, 362494082785840340⟩, ⟨(-378102448345885011), (-377360642648524807)⟩, true⟩

def words03 : List Nat := [371285206939240985, 371285207383707756, 371285208381131702, 371285209155704806, 371285210066834230, 371285210978476147, 371285211782244766, 371285211849594310, 371285212059094023, 371285212269335121]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 42530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 42500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487071128584481, 362487096948666650⟩, ⟨(-80892105654089579), (-80149768582480047)⟩, true⟩

def words04 : List Nat := [371285212879042643, 371285212880444732, 371285212825397875, 371285212710015142, 371285212596963427, 371285212598534501, 371285212695949742, 371285212990379741, 371285213286374512, 371285213332098709]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 42540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 42500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499668395300189, 362499694228090452⟩, ⟨(-616976866133489338), (-616233988270598960)⟩, true⟩

def words05 : List Nat := [371285213723941079, 371285214116517304, 371285214735785919, 371285214737188263, 371285214620394975, 371285214424235086, 371285214582831408, 371285214703235763, 371285215044408825, 371285215386233574]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 42550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 42500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488078561862040, 362488104407306649⟩, ⟨(-123722170210659486), (-122978753714034862)⟩, true⟩

def words06 : List Nat := [371285215727331409, 371285215728740734, 371285215815741641, 371285216087328717, 371285216522058227, 371285216523461021, 371285216222504424, 371285215813498733, 371285215546068314, 371285215615553718]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 42560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 42500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488974426444375, 362489000284498101⟩, ⟨(-161754486139239082), (-161010532806672330)⟩, true⟩

def words07 : List Nat := [371285216236984359, 371285216858944429, 371285217438636760, 371285217561592951, 371285217764754557, 371285217968611785, 371285218724240859, 371285218827804339, 371285218917674844, 371285219008041309]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 42570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 42500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492907756864785, 362492933627494580⟩, ⟨(-329264061115077459), (-328519572230328441)⟩, true⟩

def words08 : List Nat := [371285219156554473, 371285219158100756, 371285219452403668, 371285219830528055, 371285220045669084, 371285220047072646, 371285219599132420, 371285219578949868, 371285220088304612, 371285220270864534]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 42580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 42500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499637335922828, 362499663219343307⟩, ⟨(-615885000270206899), (-615139966567083471)⟩, true⟩

def words09 : List Nat := [371285220450963962, 371285220631558167, 371285221290171064, 371285221709394307, 371285222156329075, 371285222603752127, 371285223050767060, 371285223052174209, 371285223312272318, 371285223652981788]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 42590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 42500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 42500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk425
