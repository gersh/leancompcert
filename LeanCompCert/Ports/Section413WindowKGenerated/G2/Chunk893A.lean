import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk893A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk893A
