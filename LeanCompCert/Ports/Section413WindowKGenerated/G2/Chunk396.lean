import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk396

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571297830594190, 360571307482067888⟩, ⟨441902435622711054, 442160760840240954⟩, true⟩

def state01 : KState := ⟨⟨360594523768464294, 360594533424980219⟩, ⟨(-478069352573245157), (-477810827658137819)⟩, true⟩

def words00 : List Nat := [360582473177998552, 360582473178534598, 360582472846250261, 360582472128236441, 360582471410171543, 360582470469084808, 360582470363662005, 360582470629368301, 360582470629850749, 360582470845705318]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 39600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 39600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360611027566447561, 360611037228030930⟩, ⟨(-1132102237353359461), (-1131843511691870897)⟩, true⟩

def words01 : List Nat := [360582470935028883, 360582471024500044, 360582471096319787, 360582471096856499, 360582470831254540, 360582470038700801, 360582469246084448, 360582469027136243, 360582469748624975, 360582470470208264]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 39610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 39600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594670131290425, 360594679797979519⟩, ⟨(-484038380722231723), (-483779452746608233)⟩, true⟩

def words02 : List Nat := [360582470827063537, 360582471089254944, 360582471987054066, 360582472884967747, 360582473602617154, 360582473686711717, 360582473687203812, 360582473156761633, 360582472626244187, 360582472701192999]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 39620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 39600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573065809802564, 360573075481542025⟩, ⟨372436635628553494, 372695763775908014⟩, true⟩

def words03 : List Nat := [360582473645109804, 360582474589081701, 360582475047392034, 360582475764989092, 360582476321280175, 360582476877691175, 360582477620455541, 360582477729903750, 360582477730381798, 360582477493746261]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 39630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 39600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360605814526629349, 360605824203442542⟩, ⟨(-925977994272092215), (-925718664977609867)⟩, true⟩

def words04 : List Nat := [360582477257008812, 360582477038895191, 360582477425063940, 360582477811320733, 360582477811820049, 360582477655731075, 360582477110085068, 360582476930916705, 360582476947777083, 360582477537154741]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 39640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 39600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360587912822484262, 360587922504403114⟩, ⟨(-216125491234794538), (-215865959474993974)⟩, true⟩

def words05 : List Nat := [360582477808346710, 360582478079584428, 360582478625264119, 360582479495094266, 360582479752328396, 360582480009626337, 360582480010104583, 360582479949545594, 360582479590037310, 360582479727885251]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 39650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 39600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606554719150491, 360606564406132189⟩, ⟨(-955576904700905271), (-955317172123251669)⟩, true⟩

def words06 : List Nat := [360582480074993833, 360582480437527319, 360582480438012758, 360582480406490303, 360582480374881557, 360582480484253434, 360582481420121608, 360582482356045583, 360582482803052460, 360582483410641195]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 39660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 39600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360654731791429253, 360654741483481802⟩, ⟨(-2867045338168106429), (-2866785404405232521)⟩, true⟩

def words07 : List Nat := [360582484652125225, 360582485893711208, 360582487582526506, 360582488822103068, 360582489468926006, 360582490115768898, 360582490857957907, 360582492045650378, 360582493866887029, 360582495688153932]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 39670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 39600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593601588998041, 360593611286176526⟩, ⟨(-441279555672130338), (-441019418487437360)⟩, true⟩

def words08 : List Nat := [360582497190036655, 360582498060115017, 360582498912765530, 360582499765522937, 360582500457899731, 360582500518609671, 360582500519088160, 360582500262408560, 360582500005637522, 360582499965764155]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 39680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 39600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360520562797061772, 360520572499295375⟩, ⟨2458114917119060140, 2458375254966930576⟩, true⟩

def words09 : List Nat := [360582500520839110, 360582501075988053, 360582501244013325, 360582501244550713, 360582500987912672, 360582500361690925, 360582499735351040, 360582498945019846, 360582497868520290, 360582496309244165]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 39690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 39600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 39600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk396
