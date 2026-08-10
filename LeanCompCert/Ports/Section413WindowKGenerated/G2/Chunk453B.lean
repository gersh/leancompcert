import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk453A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk453B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk453A

def state06 : KState := ⟨⟨360611735419900184, 360611748224757236⟩, ⟨(-1293592457807128298), (-1293199953941092954)⟩, true⟩

def words05 : List Nat := [360583230987801637, 360583232387597664, 360583233418680036, 360583234694073011, 360583235768999793, 360583236843983348, 360583237612298474, 360583237895831622, 360583238524868592, 360583239154103126]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 45350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 45300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360611337710986929, 360611350521688612⟩, ⟨(-1275543984400095006), (-1275151215391644248)⟩, true⟩

def words06 : List Nat := [360583240268397740, 360583241116346411, 360583241720116452, 360583242323931786, 360583242710278567, 360583243340703414, 360583243959246199, 360583244577872097, 360583244917882080, 360583245537989958]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 45360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 45300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360653584537657543, 360653597354222063⟩, ⟨(-3192541955793798123), (-3192148920759298909)⟩, true⟩

def words07 : List Nat := [360583246479651496, 360583247421454901, 360583248478067729, 360583249554777928, 360583250153352241, 360583250751944072, 360583251835344591, 360583253164778137, 360583254715395662, 360583256266084753]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 45370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 45300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360637459693418583, 360637472515909029⟩, ⟨(-2461002202005313461), (-2460608898023546121)⟩, true⟩

def words08 : List Nat := [360583257442240630, 360583258134100195, 360583258966527648, 360583259799098719, 360583260404921292, 360583260942551330, 360583261180372975, 360583261418256750, 360583262140710261, 360583263335718605]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 45380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 45300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360566056232555487, 360566069060896403⟩, ⟨780468484008892345, 780862053573138365⟩, true⟩

def words09 : List Nat := [360583264743336277, 360583266151009826, 360583267314828191, 360583267994637785, 360583268340620268, 360583268686752680, 360583269106947487, 360583269107569156, 360583269043810732, 360583268665600658]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 45390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 45300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 45300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk453B
