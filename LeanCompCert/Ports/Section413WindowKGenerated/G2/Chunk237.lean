import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk237

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360629458519196004, 360629461828868494⟩, ⟨(-1132688938515463145), (-1132635871101628145)⟩, true⟩

def state01 : KState := ⟨⟨360642580222103456, 360642583534681933⟩, ⟨(-1443662379869905498), (-1443609243569240686)⟩, true⟩

def words00 : List Nat := [360581676614229579, 360581679977549467, 360581682447425571, 360581684917126834, 360581686198686733, 360581688397651571, 360581691864375083, 360581695330864903, 360581697442267964, 360581700010428665]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 23700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 23700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360721459692349651, 360721463007841169⟩, ⟨(-3314454313128988755), (-3314401107746066215)⟩, true⟩

def words01 : List Nat := [360581703893438396, 360581707776212767, 360581712466720886, 360581716039585708, 360581717953643518, 360581719867567818, 360581722765846634, 360581726884006157, 360581732775323548, 360581738666213664]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 23710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 23700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360644832314046337, 360644835632480578⟩, ⟨(-1496819351338277815), (-1496766076139411037)⟩, true⟩

def words02 : List Nat := [360581743664836623, 360581747772619439, 360581751819053856, 360581755865235962, 360581758833837568, 360581760039934357, 360581760040211295, 360581759890587373, 360581760786942232, 360581763445209102]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 23720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 23700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360568112061530509, 360568115382872307⟩, ⟨324183240711755344, 324236584921476206⟩, true⟩

def words03 : List Nat := [360581766860093195, 360581770274748663, 360581772796379563, 360581773556576337, 360581773556835022, 360581773466883123, 360581773376852489, 360581773775003293, 360581773775278693, 360581773200265798]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 23730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 23700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360659949892485564, 360659953216742458⟩, ⟨(-1856285143392979392), (-1856231729964248808)⟩, true⟩

def words04 : List Nat := [360581773820125422, 360581775911251045, 360581779772087765, 360581783632663514, 360581785986940596, 360581787349620653, 360581790481753643, 360581793613712956, 360581796090949553, 360581799381958060]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 23740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 23700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360682104386376897, 360682107713583997⟩, ⟨(-2382636176512552675), (-2382582693001950007)⟩, true⟩

def words05 : List Nat := [360581801145473143, 360581802908864572, 360581806441059022, 360581811152877171, 360581815408993518, 360581819664801834, 360581823030029741, 360581826443014570, 360581830663857310, 360581834884452145]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360689281878359140, 360689285208474452⟩, ⟨(-2553259533343961268), (-2553205980719518954)⟩, true⟩

def words06 : List Nat := [360581840872173785, 360581845345286164, 360581848855182107, 360581852364817670, 360581854484921472, 360581857873963898, 360581863029476489, 360581868184614234, 360581872251456259, 360581876770431479]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360660711901703042, 360660715234741195⟩, ⟨(-1873937962061181302), (-1873884339946418870)⟩, true⟩

def words07 : List Nat := [360581881547279462, 360581886323819937, 360581892865829756, 360581897651839289, 360581900929995317, 360581904207899398, 360581907191836573, 360581911064943359, 360581914379082431, 360581917693008450]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360706534218027970, 360706537554012589⟩, ⟨(-2964145613696204111), (-2964091921499994919)⟩, true⟩

def words08 : List Nat := [360581920118661691, 360581923169041005, 360581926774416578, 360581930379578584, 360581933158237440, 360581935982977775, 360581937909474620, 360581939835841054, 360581943525852638, 360581948763230361]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617030334506735, 360617033673410222⟩, ⟨(-834320672852771860), (-834266911202132032)⟩, true⟩

def words09 : List Nat := [360581954983203488, 360581961202712705, 360581965725154345, 360581968494560659, 360581970810492635, 360581973126314739, 360581976609368078, 360581978968357330, 360581980441520064, 360581981914610083]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk237
