import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk726A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484691351211598, 362484769796120113⟩, ⟨33230282156795063, 37076392455927259⟩, true⟩

def state01 : KState := ⟨⟨362478551712163621, 362478630179255223⟩, ⟨479026991953597389, 482874712861874627⟩, true⟩

def words00 : List Nat := [371285280647311166, 371285280649805733, 371285280600466684, 371285280551768336, 371285280502100804, 371285280491538077, 371285280397245542, 371285280412454601, 371285280427505274, 371285280430086540]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 72600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 72600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492895679046467, 362492974168676881⟩, ⟨(-562625259781509983), (-558775902217673583)⟩, true⟩

def words01 : List Nat := [371285280340234669, 371285280231096216, 371285280197954901, 371285280200448040, 371285280027042540, 371285279820752254, 371285279613428592, 371285279596615556, 371285279647829965, 371285279756561685]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 72610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 72600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483953445063994, 362484031957193763⟩, ⟨86784475695312361, 90635467275141259⟩, true⟩

def words02 : List Nat := [371285279863234621, 371285279865744889, 371285279926131452, 371285280053178662, 371285280192254839, 371285280194748259, 371285280081363418, 371285279957513419, 371285279861070581, 371285279863944075]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 72620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 72600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466611251791817, 362466689786424059⟩, ⟨1346483128661130386, 1350335754710786282⟩, true⟩

def words03 : List Nat := [371285279914440228, 371285279983191417, 371285280022910583, 371285280025407939, 371285279861295150, 371285279755676588, 371285279680141309, 371285279682635202, 371285279463436861, 371285279210360056]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 72630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 72600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486788520200998, 362486867077157440⟩, ⟨(-119281297422347884), (-115427049627818874)⟩, true⟩

def words04 : List Nat := [371285278956148122, 371285278823901261, 371285278595529116, 371285278557433542, 371285278518555786, 371285278443483839, 371285278209596780, 371285278166290455, 371285278264529441, 371285278288983461]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 72640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 72600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk726A
