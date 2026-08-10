import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk355A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360505057996393125, 360505065683797235⟩, ⟨2731405455125728225, 2731589950558868609⟩, true⟩

def state01 : KState := ⟨⟨360583087985200123, 360583095677098826⟩, ⟨(-39110542610990864), (-38925887597593182)⟩, true⟩

def words00 : List Nat := [360582009712535548, 360582008141560302, 360582007105904283, 360582006304277057, 360582005502654031, 360582004017474109, 360582002091467895, 360582000957672433, 360581999823797991, 360581999512879357]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 35500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 35500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577272893901041, 360577280590345277⟩, ⟨167332536297703111, 167517352745577409⟩, true⟩

def words01 : List Nat := [360581999513312114, 360581998892761889, 360581998272155839, 360581997962226075, 360581997962625013, 360581997812100277, 360581997661529791, 360581997111680385, 360581996864267413, 360581996732032935]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 35510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 35500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594067263198619, 360594074964130904⟩, ⟨(-429422342656701601), (-429237366771280555)⟩, true⟩

def words02 : List Nat := [360581997258128233, 360581997258604967, 360581997127869016, 360581996601859875, 360581996075810375, 360581994917083984, 360581994304756529, 360581994394401860, 360581994394828545, 360581994319995606]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 35520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 35500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360644836699900278, 360644844405334891⟩, ⟨(-2233461023075744256), (-2233275887200360180)⟩, true⟩

def words03 : List Nat := [360581995451292795, 360581996582680451, 360581998504724087, 360581999864755148, 360582000469455431, 360582001074158438, 360582002469450042, 360582004260179163, 360582006028724201, 360582007797270955]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 35530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 35500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360651189860099916, 360651197570080501⟩, ⟨(-2459464720194325622), (-2459279422732899180)⟩, true⟩

def words04 : List Nat := [360582008951377470, 360582009884931073, 360582011608791184, 360582013332693930, 360582014857582078, 360582016408666085, 360582017334641055, 360582018260614774, 360582019526697569, 360582021473128717]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 35540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 35500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk355A
