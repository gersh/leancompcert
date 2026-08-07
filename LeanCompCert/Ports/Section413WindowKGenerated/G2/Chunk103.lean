import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk103

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360477156773866063, 360477157352717415⟩, ⟨1063824258889639968, 1063828300143457518⟩, true⟩

def state01 : KState := ⟨⟨360611215145286649, 360611215725314898⟩, ⟨(-316946575877910441), (-316942522496046071)⟩, true⟩

def words00 : List Nat := [360580431627174696, 360580437476049422, 360580453346492514, 360580469213881403, 360580476775354430, 360580476775479177, 360580475024071316, 360580474479219641, 360580474452392890, 360580477433927444]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 10300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 10300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360691158451596008, 360691159032814437⟩, ⟨(-1141792609387908237), (-1141788543729323623)⟩, true⟩

def words01 : List Nat := [360580477434040551, 360580473285867540, 360580474374899650, 360580484559823075, 360580492238931509, 360580499916571598, 360580501959851653, 360580509885974334, 360580520607892356, 360580531327773325]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 10310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 10300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360662997138415305, 360662997720810011⟩, ⟨(-850808658666675966), (-850804580862944142)⟩, true⟩

def words02 : List Nat := [360580551413988339, 360580569140153288, 360580580460506219, 360580591778678925, 360580595734100213, 360580604380700849, 360580617033878996, 360580629684630737, 360580635224953438, 360580643197447032]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 10320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 10300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360813618023850669, 360813618607428535⟩, ⟨(-2407300322110831278), (-2407296232079311858)⟩, true⟩

def words03 : List Nat := [360580660520017863, 360580677839275680, 360580704504983275, 360580721910161833, 360580731131447747, 360580740350959421, 360580758912049886, 360580782140217668, 360580804658354398, 360580827172163154]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 10330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 10300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360844787200638324, 360844787785408684⟩, ⟨(-2730639515357632368), (-2730635412989860710)⟩, true⟩

def words04 : List Nat := [360580844830289295, 360580853243027228, 360580870988473019, 360580888730524394, 360580903994732024, 360580919679984116, 360580930587615965, 360580941493154051, 360580958276763168, 360580983765218378]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 10340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 10300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360620369883374115, 360620370469326822⟩, ⟨(-406697062059326736), (-406692947448282938)⟩, true⟩

def words05 : List Nat := [360581010447165334, 360581037123981012, 360581054750458776, 360581067649856020, 360581076041243007, 360581084431042274, 360581102124195901, 360581110603511153, 360581114393186351, 360581118182149110]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 10350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 10300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360801196587983711, 360801197175121346⟩, ⟨(-2281170746967986677), (-2281166620075100393)⟩, true⟩

def words06 : List Nat := [360581124443446647, 360581138154015866, 360581157137860487, 360581176118065847, 360581187273249227, 360581193368523211, 360581199046387551, 360581204723192780, 360581219680287617, 360581240891245626]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 10360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 10300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360674628007684269, 360674628596018901⟩, ⟨(-968073348306025590), (-968069208994374816)⟩, true⟩

def words07 : List Nat := [360581257349304208, 360581273804203214, 360581286365655763, 360581306528015885, 360581323693575046, 360581340855846157, 360581353358468737, 360581356680464738, 360581365666300294, 360581374650445799]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 10370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 10300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360527698652135951, 360527699241657577⟩, ⟨557619575449977733, 557623727088672829⟩, true⟩

def words08 : List Nat := [360581383230035656, 360581387563746664, 360581387563858810, 360581387161590988, 360581386759379484, 360581381838597976, 360581381768447189, 360581378924866653, 360581376081817706, 360581368512792195]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 10380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 10300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360661007992045308, 360661008582755975⟩, ⟨(-828396468689545866), (-828392304690850088)⟩, true⟩

def words09 : List Nat := [360581367425043234, 360581371501522724, 360581379189588457, 360581379189714474, 360581377729149773, 360581366646306380, 360581355565570894, 360581349382487967, 360581355476404665, 360581363134751856]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 10390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 10300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 10300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk103
