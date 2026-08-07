import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk466

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362459659074475885, 362459690273468262⟩, ⟨1196923310495521909, 1197905591013936529⟩, true⟩

def state01 : KState := ⟨⟨362479337329186870, 362479368542026303⟩, ⟨279892753049979448, 280875678912621442⟩, true⟩

def words00 : List Nat := [371285395851458885, 371285395761176665, 371285395462936374, 371285395487670162, 371285395488873409, 371285395465012640, 371285395058455726, 371285394779159992, 371285394622357636, 371285394623959636]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 46600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 46600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492811517210532, 362492842744165314⟩, ⟨(-348241607097011865), (-347258023248297309)⟩, true⟩

def words01 : List Nat := [371285394495843072, 371285394367176269, 371285394299576000, 371285394301285515, 371285394196833676, 371285394216051599, 371285394217209479, 371285394188761334, 371285394050167758, 371285394211889124]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 46610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 46600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362468306630832285, 362468337871559221⟩, ⟨794350816583715157, 795335042562268795⟩, true⟩

def words02 : List Nat := [371285394699784961, 371285394701332813, 371285394576753470, 371285394453453406, 371285394337251222, 371285394338960305, 371285394205912427, 371285394236548259, 371285394237725756, 371285394166703169]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 46620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 46600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362506261160622731, 362506292415360959⟩, ⟨(-975692233419445397), (-974707354024785903)⟩, true⟩

def words03 : List Nat := [371285393801990272, 371285393616903822, 371285393702957832, 371285393704532904, 371285393595771203, 371285393412042221, 371285393445253057, 371285393446974796, 371285393885415732, 371285394335259230]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 46630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 46600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489900551725667, 362489931820443544⟩, ⟨(-212645181018755728), (-211659649543549504)⟩, true⟩

def words04 : List Nat := [371285394689927443, 371285394691475913, 371285394634111264, 371285394836113384, 371285395142181386, 371285395143730128, 371285394905292758, 371285394662876613, 371285394634333871, 371285394733359805]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 46640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 46600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362455040394141344, 362455071676783423⟩, ⟨1413834116978625600, 1414820298087268372⟩, true⟩

def words05 : List Nat := [371285395069323427, 371285395405880675, 371285395742652428, 371285395744201159, 371285395469153865, 371285395206413489, 371285394942847027, 371285394855266688, 371285394234438142, 371285393586300939]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 46650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 46600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362463687359709634, 362463718656236636⟩, ⟨1010431812136320980, 1011418641186395542⟩, true⟩

def words06 : List Nat := [371285392937519225, 371285392634573356, 371285392224074834, 371285392249196942, 371285392250411046, 371285392139078651, 371285391415801898, 371285391020163839, 371285390623776735, 371285390364854301]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 46660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 46600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362462271673000547, 362462302983649845⟩, ⟨1076515156457108080, 1077502644668140778⟩, true⟩

def words07 : List Nat := [371285389901663038, 371285389413831657, 371285388925379071, 371285388675168019, 371285388196417090, 371285387855950659, 371285387514961877, 371285387175051146, 371285386223532151, 371285385730964930]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 46670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 46600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472098324768200, 362472129649250958⟩, ⟨617763082112071256, 618751216139974372⟩, true⟩

def words08 : List Nat := [371285385237538493, 371285385202646311, 371285384697583516, 371285384123965682, 371285383549782853, 371285383116242649, 371285382484279889, 371285382310894741, 371285382136973345, 371285381977718296]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 46680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 46600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487226513444609, 362487257851915973⟩, ⟨(-88567756292379404), (-87578969064982254)⟩, true⟩

def words09 : List Nat := [371285381868985874, 371285382044878609, 371285382608568967, 371285382645274616, 371285382646483121, 371285382558363191, 371285382563428562, 371285382565137702, 371285382497530572, 371285382539415920]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 46690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 46600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 46600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk466
