import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk846

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485765581135311, 362485873366413821⟩, ⟨(-53161164499704075), (-47004087099738967)⟩, true⟩

def state01 : KState := ⟨⟨362476246157034955, 362476353968511252⟩, ⟨752264274305982553, 758423568175880895⟩, true⟩

def words00 : List Nat := [371285317849607936, 371285317852596596, 371285317817461933, 371285317783238987, 371285317753199984, 371285317756437955, 371285317716198974, 371285317738126713, 371285317740388414, 371285317726556116]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 84600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 84600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488891921441972, 362488999759436118⟩, ⟨(-317738936972468965), (-311577399290757259)⟩, true⟩

def words01 : List Nat := [371285317643874841, 371285317668649177, 371285317823931592, 371285317826869575, 371285317796280367, 371285317743898132, 371285317694651697, 371285317697922959, 371285317678648094, 371285317725434030]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 84610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 84600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480909736187291, 362481017600740271⟩, ⟨357680762025525343, 363844547245698385⟩, true⟩

def words02 : List Nat := [371285317759761586, 371285317762702453, 371285317644829312, 371285317538500025, 371285317430679592, 371285317367941231, 371285317200336687, 371285317033719093, 371285316865935883, 371285316839157449]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 84620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 84600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475168588490867, 362475276479505860⟩, ⟨843653378545582843, 849819403380498331⟩, true⟩

def words03 : List Nat := [371285316879111383, 371285316971086225, 371285317061958868, 371285317064917930, 371285317036451416, 371285317046036416, 371285317104774208, 371285317107713628, 371285316994160323, 371285316878884175]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 84630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 84600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480059176390759, 362480167093703029⟩, ⟨429705495049002649, 435873745822007245⟩, true⟩

def words04 : List Nat := [371285316763418760, 371285316766657965, 371285316700154056, 371285316691269337, 371285316681485472, 371285316639798525, 371285316411151890, 371285316302419931, 371285316219372399, 371285316222419178]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 84640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 84600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488684767820466, 362488792711931381⟩, ⟨(-300507950840219440), (-294337431428849266)⟩, true⟩

def words05 : List Nat := [371285316163829172, 371285316071872794, 371285316023124495, 371285316026394471, 371285316020481336, 371285316041091806, 371285316060555598, 371285316063546643, 371285316008200687, 371285316052886144]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470715665263025, 362470823635522728⟩, ⟨1220870802034765725, 1227043535339093019⟩, true⟩

def words06 : List Nat := [371285316213514463, 371285316216454511, 371285316191362739, 371285316155445315, 371285316118406553, 371285316059042345, 371285315933246013, 371285315859252652, 371285315784304507, 371285315705149977]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483689222621239, 362483797219541387⟩, ⟨122360024819205663, 128535015589566951⟩, true⟩

def words07 : List Nat := [371285315535986641, 371285315491201016, 371285315535721405, 371285315538661913, 371285315446021817, 371285315334556806, 371285315221929533, 371285315198637327, 371285315125199687, 371285315110608813]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478912239746218, 362479020263211823⟩, ⟨526874571042476678, 533051809820635594⟩, true⟩

def words08 : List Nat := [371285315094902858, 371285315067775089, 371285314906283187, 371285314849101865, 371285314790499137, 371285314775498651, 371285314667226673, 371285314559950749, 371285314451454169, 371285314416120321]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476491654433562, 362476599704390321⟩, ⟨731939357912069460, 738118840358895440⟩, true⟩

def words09 : List Nat := [371285314408825717, 371285314477021789, 371285314508244201, 371285314511195252, 371285314431640511, 371285314379397161, 371285314409145367, 371285314412086789, 371285314312068102, 371285314212540958]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk846
