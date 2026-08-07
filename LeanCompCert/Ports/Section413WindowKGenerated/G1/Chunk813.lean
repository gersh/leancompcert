import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk813

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491279681283571, 362491378917266518⟩, ⟨(-508882104134716793), (-503434292745056821)⟩, true⟩

def state01 : KState := ⟨⟨362483303734889943, 362483402995910081⟩, ⟨139597607413283714, 145047454458423322⟩, true⟩

def words00 : List Nat := [371285186817287928, 371285186826337986, 371285186828442286, 371285186827054754, 371285186824601519, 371285186805278935, 371285186762927104, 371285186819439711, 371285186875106715, 371285186878021242]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 81300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 81300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492171048494021, 362492270335035781⟩, ⟨(-581443349931796988), (-575991427601178072)⟩, true⟩

def words01 : List Nat := [371285186931166102, 371285187007826705, 371285187172494945, 371285187175309689, 371285187156736119, 371285187124863154, 371285187192113769, 371285187219830442, 371285187308874448, 371285187399169263]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 81310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 81300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486678437645657, 362486777749590506⟩, ⟨(-134810608152352254), (-129356619915402016)⟩, true⟩

def words02 : List Nat := [371285187488453684, 371285187491268886, 371285187399739175, 371285187387048766, 371285187401243822, 371285187404109477, 371285187326846182, 371285187250697087, 371285187230949162, 371285187253716665]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 81320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 81300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485139215482906, 362485238552760307⟩, ⟨(-9562680497344195), (-4106631831711947)⟩, true⟩

def words03 : List Nat := [371285187426302991, 371285187600005618, 371285187742836872, 371285187750967146, 371285187804725055, 371285187859899544, 371285188049102675, 371285188059601400, 371285188062331155, 371285188066144312]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 81330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 81300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488915877975019, 362489015240440376⟩, ⟨(-316744201194162282), (-311286103612836946)⟩, true⟩

def words04 : List Nat := [371285188168832820, 371285188197519454, 371285188376060816, 371285188555788144, 371285188670078046, 371285188672894043, 371285188603552365, 371285188598098367, 371285188733482414, 371285188783437846]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 81340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 81300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362498435014680726, 362498534402869606⟩, ⟨(-1091168102523374701), (-1085707912208851389)⟩, true⟩

def words05 : List Nat := [371285188819244698, 371285188856001921, 371285189042636163, 371285189189852996, 371285189370911081, 371285189553039394, 371285189725045979, 371285189740848336, 371285189906778293, 371285190074355836]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483464256048023, 362483563669334562⟩, ⟨126934083235617349, 132396315627777953⟩, true⟩

def words06 : List Nat := [371285190288197123, 371285190348516793, 371285190394409559, 371285190441225801, 371285190533415526, 371285190558567265, 371285190624179920, 371285190690994025, 371285190756446700, 371285190759363170]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362508909396069082, 362509008834802614⟩, ⟨(-1943638615043992651), (-1938174311902587095)⟩, true⟩

def words07 : List Nat := [371285190872286062, 371285191006631697, 371285191290544199, 371285191456212695, 371285191596482293, 371285191737623031, 371285191989258107, 371285192190159182, 371285192484734676, 371285192780540531]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492083050635198, 362492182514774928⟩, ⟨(-574210034565094456), (-568743663732497376)⟩, true⟩

def words08 : List Nat := [371285193075359341, 371285193245615256, 371285193541178823, 371285193838221076, 371285194155306330, 371285194272038186, 371285194387736078, 371285194504337377, 371285194630202818, 371285194719272570]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481762045425616, 362481861534989239⟩, ⟨265929635548919186, 271398075754231064⟩, true⟩

def words09 : List Nat := [371285194950432238, 371285195182770110, 371285195412061508, 371285195440904980, 371285195501466346, 371285195563495795, 371285195731519069, 371285195734336798, 371285195701425643, 371285195663684009]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk813
