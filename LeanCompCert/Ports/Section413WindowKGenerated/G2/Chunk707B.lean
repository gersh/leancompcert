import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk707A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk707B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk707A

def state06 : KState := ⟨⟨360602732560976836, 360602764859159910⟩, ⟨(-1441081400322186013), (-1439537695163429991)⟩, true⟩

def words05 : List Nat := [360582419971802297, 360582419980098184, 360582420187390502, 360582420329519686, 360582420330444918, 360582420297479333, 360582420393219654, 360582420622718786, 360582420911043871, 360582421199585238]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 70750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 70700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581575939903126, 360581608247642064⟩, ⟨55873448873009020, 57417830252347760⟩, true⟩

def words06 : List Nat := [360582421369414385, 360582421370417224, 360582421340733323, 360582421205840038, 360582421070684918, 360582420885471961, 360582420584526641, 360582420182525168, 360582419780343118, 360582419577728999]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 70760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 70700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360546199270450374, 360546231587634943⟩, ⟨2559686395850708048, 2561231445745012420⟩, true⟩

def words07 : List Nat := [360582419567079213, 360582419530736413, 360582419494281392, 360582419346561969, 360582419169851373, 360582418886727404, 360582418603320989, 360582418315882933, 360582417905218543, 360582417395006306]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 70770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 70700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360570427020157943, 360570459346809911⟩, ⟨844755866136286073, 846301586179511399⟩, true⟩

def words08 : List Nat := [360582416884581675, 360582416490537814, 360582416214194933, 360582416137194540, 360582416060120378, 360582415789772728, 360582415319949814, 360582414992859808, 360582414665482459, 360582414447617646]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 70780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 70700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589720175274729, 360589752511498878⟩, ⟨(-521156546454581941), (-519610148751006433)⟩, true⟩

def words09 : List Nat := [360582414279648404, 360582413956819427, 360582413633807528, 360582413526289367, 360582413527129162, 360582413494110392, 360582413460976576, 360582413328331598, 360582413383958086, 360582413488762603]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 70790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 70700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 70700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk707B
