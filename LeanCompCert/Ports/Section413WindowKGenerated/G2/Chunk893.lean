import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk893

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580823417924487, 360580875803851700⟩, ⟨102653137197238290, 105812173742109872⟩, true⟩

def state01 : KState := ⟨⟨360569820554569822, 360569872952754745⟩, ⟨1085190341923081345, 1088350473142142021⟩, true⟩

def words00 : List Nat := [360582060698494262, 360582060593959088, 360582060363935876, 360582060259502740, 360582060154730326, 360582059997592881, 360582059843150275, 360582059626604808, 360582059409825841, 360582059163404641]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 89300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 89300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360554445166754289, 360554497577086539⟩, ⟨2458419057089050620, 2461580273245112746⟩, true⟩

def words01 : List Nat := [360582059027999982, 360582058907279938, 360582058786442178, 360582058569695531, 360582058227536198, 360582057854143007, 360582057480365102, 360582057232023565, 360582057000626337, 360582056693446203]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 89310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 89300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569491755572702, 360569544178042226⟩, ⟨1114391405152467642, 1117553705472244686⟩, true⟩

def words02 : List Nat := [360582056385947107, 360582056183164721, 360582056042893983, 360582055940412562, 360582055837845865, 360582055628831077, 360582055336900203, 360582055041163201, 360582054745054335, 360582054574386929]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 89320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 89300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360566928249160017, 360566980683899417⟩, ⟨1343395418410655399, 1346558814858625519⟩, true⟩

def words03 : List Nat := [360582054435496879, 360582054202009785, 360582053968279160, 360582053834439158, 360582053796815360, 360582053686309251, 360582053575659098, 360582053388123550, 360582053145909862, 360582052978670613]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 89330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 89300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360566839646042819, 360566892092928292⟩, ⟨1351301168518582635, 1354465650157520001⟩, true⟩

def words04 : List Nat := [360582052811024834, 360582052640742282, 360582052490774707, 360582052278725898, 360582052066471666, 360582051808478681, 360582051612924289, 360582051503458507, 360582051393838894, 360582051193657532]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 89340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 89300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360580215788618066, 360580268247661166⟩, ⟨156043146166398688, 159208714148104058⟩, true⟩

def words05 : List Nat := [360582051025041145, 360582050964294352, 360582050903160044, 360582050861570027, 360582050740530049, 360582050490536506, 360582050240303707, 360582050045708664, 360582049921526439, 360582049902922448]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 89350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 89300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574384019573126, 360574436490917967⟩, ⟨677204794141353227, 680371461466564113⟩, true⟩

def words06 : List Nat := [360582049884143769, 360582049803410516, 360582049868811595, 360582049964937845, 360582050012867961, 360582050014156817, 360582049937098891, 360582049797381248, 360582049657440791, 360582049464639200]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 89360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 89300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360563442006137318, 360563494489620728⟩, ⟨1655168712370485384, 1658336464579889092⟩, true⟩

def words07 : List Nat := [360582049420334640, 360582049461460193, 360582049462609459, 360582049434657143, 360582049281469153, 360582049025748458, 360582048769626621, 360582048615847223, 360582048471487341, 360582048265236973]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 89370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 89300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360599424215182075, 360599476710850779⟩, ⟨(-1561139881643587662), (-1557971040252490538)⟩, true⟩

def words08 : List Nat := [360582048058698106, 360582047977534242, 360582047958783337, 360582047929317680, 360582047899752933, 360582047750454127, 360582047662301859, 360582047681634450, 360582047790819155, 360582047987150938]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 89380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 89300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594487931376959, 360594540439311716⟩, ⟨(-1119846681461592013), (-1116676743548369569)⟩, true⟩

def words09 : List Nat := [360582048114552762, 360582048242092983, 360582048494343766, 360582048818808255, 360582049083676854, 360582049348747665, 360582049489702672, 360582049505762408, 360582049646524136, 360582049787713319]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 89390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 89300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 89300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk893
