import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk820A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360574281939940936, 360574325820400155⟩, ⟨651014260065630362, 653444329874095360⟩, true⟩

def state01 : KState := ⟨⟨360609205617569529, 360609249509119732⟩, ⟨(-2212919040757849518), (-2210488061435555328)⟩, true⟩

def words00 : List Nat := [360582294557461734, 360582294639229261, 360582294871060881, 360582295103120222, 360582295179357847, 360582295180532983, 360582295252759125, 360582295364004791, 360582295623481141, 360582295953359706]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602536755594624, 360602580658347078⟩, ⟨(-1665933363435738309), (-1663501465360684673)⟩, true⟩

def words01 : List Nat := [360582296208586563, 360582296463956939, 360582296867655035, 360582297346266769, 360582297762122830, 360582298178168110, 360582298499843945, 360582298752269110, 360582299000515778, 360582299249130406]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597581259641232, 360597625173466374⟩, ⟨(-1259477323611019470), (-1257044517300083036)⟩, true⟩

def words02 : List Nat := [360582299645903504, 360582299894604845, 360582300051441418, 360582300208400064, 360582300275439675, 360582300455887304, 360582300658264616, 360582300860855727, 360582300967473624, 360582301155506090]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360620440107790547, 360620484032716211⟩, ⟨(-3134768460238560199), (-3132334743295781379)⟩, true⟩

def words03 : List Nat := [360582301491786071, 360582301828403000, 360582302160739807, 360582302345020405, 360582302403005232, 360582302461069765, 360582302667410845, 360582302985618850, 360582303451964606, 360582303918586742]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602124826116941, 360602168762238708⟩, ⟨(-1632148207973898904), (-1629713572448777752)⟩, true⟩

def words04 : List Nat := [360582304262778427, 360582304633543623, 360582305048395741, 360582305463591363, 360582305816656317, 360582306021677187, 360582306112470650, 360582306203371800, 360582306316381015, 360582306559798168]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk820A
