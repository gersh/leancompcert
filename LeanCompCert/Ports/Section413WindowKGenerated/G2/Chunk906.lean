import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk906

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360595173871657791, 360595227854397005⟩, ⟨(-1200035505916341479), (-1196732833514442671)⟩, true⟩

def state01 : KState := ⟨⟨360587692167263079, 360587746162334011⟩, ⟨(-522238344463826857), (-518934554746545775)⟩, true⟩

def words00 : List Nat := [360582019148157646, 360582019176949315, 360582019178125674, 360582019146106410, 360582019113874429, 360582019051399870, 360582019065518937, 360582019082679243, 360582019083844708, 360582019103204915]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360601762013269974, 360601816020684429⟩, ⟨(-1797262875472472086), (-1793957967247539372)⟩, true⟩

def words01 : List Nat := [360582019211983061, 360582019321155775, 360582019441050668, 360582019442358953, 360582019440815156, 360582019324199967, 360582019211059382, 360582019309332397, 360582019528848480, 360582019748658657]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581532697618623, 360581586717523236⟩, ⟨36006307653215218, 39312347796590892⟩, true⟩

def words02 : List Nat := [360582019907511796, 360582020069519334, 360582020267908305, 360582020466672600, 360582020611886932, 360582020659997695, 360582020661166591, 360582020625386469, 360582020589382129, 360582020485015199]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565630970988461, 360565685003211395⟩, ⟨1477318038565153471, 1480625195179223081⟩, true⟩

def words03 : List Nat := [360582020598110055, 360582020716239277, 360582020773210296, 360582020774518854, 360582020709867711, 360582020615046659, 360582020525182913, 360582020526491515, 360582020411496450, 360582020232637468]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579743188612127, 360579797233202794⟩, ⟨198115350777030350, 201423628462420770⟩, true⟩

def words04 : List Nat := [360582020053476217, 360582019998746950, 360582019999824764, 360582019961907467, 360582019923884250, 360582019782421935, 360582019556009212, 360582019451568267, 360582019346738986, 360582019225794768]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360574057817602523, 360574111874640931⟩, ⟨713512170794008824, 716821576929651560⟩, true⟩

def words05 : List Nat := [360582019202457896, 360582019068011812, 360582018933317772, 360582018935995496, 360582018945152303, 360582018954522534, 360582018955720169, 360582018869765215, 360582018662070119, 360582018576349840]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 90650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 90600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584855925627285, 360584909994996391⟩, ⟨(-265501141078404112), (-262190616980955808)⟩, true⟩

def words06 : List Nat := [360582018490199068, 360582018445312830, 360582018440700135, 360582018366748531, 360582018292562149, 360582018188223957, 360582018226130694, 360582018289455522, 360582018291678205, 360582018324925686]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 90660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 90600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360598245228683033, 360598299310426193⟩, ⟨(-1479682308813538769), (-1476370662700289779)⟩, true⟩

def words07 : List Nat := [360582018355135817, 360582018385711451, 360582018434561773, 360582018435870945, 360582018363428008, 360582018190057335, 360582018016439553, 360582018022789996, 360582018203394827, 360582018384292822]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 90670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 90600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360569454945704060, 360569509039913288⟩, ⟨1131068331769014496, 1134381108366707984⟩, true⟩

def words08 : List Nat := [360582018498597645, 360582018499906938, 360582018493361353, 360582018495520937, 360582018496635729, 360582018414658916, 360582018211115692, 360582017914009732, 360582017616654553, 360582017377198179]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 90680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 90600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360547626011616790, 360547680118169101⟩, ⟨3110892860784399717, 3114206756838352455⟩, true⟩

def words09 : List Nat := [360582017240334182, 360582017196573682, 360582017152659805, 360582017046974818, 360582016849417897, 360582016533949530, 360582016218103393, 360582016023941751, 360582015740763870, 360582015363558719]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 90600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 90600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk906
