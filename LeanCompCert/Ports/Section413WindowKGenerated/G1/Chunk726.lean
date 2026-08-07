import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk726

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

def state06 : KState := ⟨⟨362480469851492550, 362480548431183587⟩, ⟨339788820659990003, 343644720236174481⟩, true⟩

def words05 : List Nat := [371285278297771692, 371285278307380158, 371285278363820715, 371285278366569399, 371285278328021001, 371285278298526650, 371285278268183439, 371285278223199614, 371285277982841284, 371285277920864790]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 72650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 72600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477674667356410, 362477753269247897⟩, ⟨542927463055242750, 546784975831784556⟩, true⟩

def words06 : List Nat := [371285277981560727, 371285277984056415, 371285277892840774, 371285277799959383, 371285277706100530, 371285277670642146, 371285277567339696, 371285277540965736, 371285277513771187, 371285277487987842]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 72660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 72600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507554990163552, 362507633614624832⟩, ⟨(-1628601517796700915), (-1624742364759994049)⟩, true⟩

def words07 : List Nat := [371285277471740460, 371285277560358713, 371285277836773307, 371285277992346953, 371285278109826110, 371285278228026514, 371285278443187827, 371285278564425042, 371285278873699284, 371285279184102963]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 72670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 72600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491600095280630, 362491678742285381⟩, ⟨(-468989298616404190), (-465128507005023322)⟩, true⟩

def words08 : List Nat := [371285279454089639, 371285279472497938, 371285279615065549, 371285279758918056, 371285279958878218, 371285279961373696, 371285279909307017, 371285279858861252, 371285279943084475, 371285280033958284]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 72680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 72600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482472303601456, 362482550973036076⟩, ⟨194625125306069900, 198487547458905998⟩, true⟩

def words09 : List Nat := [371285280296676734, 371285280560388243, 371285280813698560, 371285280871410282, 371285280932433683, 371285280994693902, 371285281229951197, 371285281233542112, 371285281235420560, 371285281200648991]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 72690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 72600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 72600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk726
