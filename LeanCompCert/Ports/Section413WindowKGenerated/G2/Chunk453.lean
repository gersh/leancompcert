import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk453

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586834977697362, 360586847747307471⟩, ⟨(-165096821599666074), (-164705915478014322)⟩, true⟩

def state01 : KState := ⟨⟨360578941236219886, 360578954011670037⟩, ⟨192459285854457053, 192850456559522661⟩, true⟩

def words00 : List Nat := [360583212380459331, 360583212381079490, 360583212340201233, 360583212054847147, 360583211769398028, 360583211050473188, 360583210595842025, 360583210612112679, 360583210612669065, 360583210256573139]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 45300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 45300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360623805928153932, 360623818709467857⟩, ⟨(-1840752547463579673), (-1840361111042383839)⟩, true⟩

def words01 : List Nat := [360583210163149462, 360583210057890199, 360583210235762853, 360583210236383282, 360583210173419032, 360583209706147842, 360583209257123648, 360583209667717621, 360583210564270573, 360583211460928717]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 45310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 45300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360625180218078745, 360625193005293390⟩, ⟨(-1903183345523991895), (-1902791641652670037)⟩, true⟩

def words02 : List Nat := [360583212113052929, 360583212848667120, 360583213922933859, 360583214997341270, 360583215680300017, 360583216009940417, 360583216035652113, 360583216061429919, 360583216573047089, 360583217499752973]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 45320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 45300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360568133927955084, 360568146721022668⟩, ⟨683044695541771586, 683436664756407006⟩, true⟩

def words03 : List Nat := [360583218264499393, 360583219029335817, 360583219471550430, 360583219707551418, 360583219820097341, 360583219932802606, 360583220531130605, 360583220644356882, 360583220644920978, 360583220313099343]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 45330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 45300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360657738454813714, 360657751253740103⟩, ⟨(-3380024297567645641), (-3379632062685601093)⟩, true⟩

def words04 : List Nat := [360583220134449147, 360583220671948818, 360583221694942674, 360583222718013177, 360583223328902001, 360583224118911916, 360583225275437587, 360583226432094178, 360583227944106965, 360583229588006479]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 45340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 45300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk453
