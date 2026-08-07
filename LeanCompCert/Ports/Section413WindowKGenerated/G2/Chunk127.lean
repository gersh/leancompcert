import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk127

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360498695623336251, 360498696521190028⟩, ⟨1052116584024402531, 1052124308204280333⟩, true⟩

def state01 : KState := ⟨⟨360632579124821035, 360632580024149179⟩, ⟨(-648924875334803307), (-648917132423126377)⟩, true⟩

def words00 : List Nat := [360581534432363861, 360581529613210730, 360581534028058504, 360581539318831206, 360581539318978591, 360581538167253449, 360581530861470824, 360581527382647778, 360581524388076767, 360581528404888450]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 12700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 12700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360538867768515192, 360538868669334778⟩, ⟨543062151226007437, 543069913101209481⟩, true⟩

def words01 : List Nat := [360581528405028087, 360581528335623953, 360581534354750570, 360581544603937973, 360581553244439351, 360581561883608712, 360581567116576070, 360581567116732526, 360581566201439214, 360581562844893050]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 12710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 12700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360514204824517916, 360514205726811474⟩, ⟨856841606661281913, 856849387292842325⟩, true⟩

def words02 : List Nat := [360581562284472074, 360581562284628591, 360581558934473763, 360581552499388124, 360581546065288612, 360581537974095975, 360581534908924173, 360581529359767218, 360581523811464999, 360581515183786560]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 12720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 12700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360559774664080711, 360559775567855009⟩, ⟨275925665713593849, 275933465202273743⟩, true⟩

def words03 : List Nat := [360581509896861669, 360581507717446658, 360581505538331017, 360581500419342161, 360581489163769889, 360581472814458853, 360581456467685294, 360581443930106810, 360581436095611718, 360581434395578893]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 12730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 12700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360445844352995980, 360445845258262948⟩, ⟨1727780590044409247, 1727788408557015869⟩, true⟩

def words04 : List Nat := [360581432695787150, 360581427346421182, 360581419478876882, 360581417743622385, 360581416008597283, 360581412672971738, 360581403210619164, 360581388919349440, 360581374630292969, 360581358074620362]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 12740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 12700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360384023485039962, 360384024391784389⟩, ⟨2516615525519956799, 2516623362877719213⟩, true⟩

def words05 : List Nat := [360581347447124885, 360581340109915807, 360581332773842231, 360581321671724844, 360581310862452688, 360581298460910729, 360581286061267489, 360581279781035109, 360581267385811399, 360581251928060073]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 12750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 12700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360513115575616836, 360513116483845974⟩, ⟨868616095661564812, 868623951971717020⟩, true⟩

def words06 : List Nat := [360581236472697184, 360581220815352065, 360581208281346049, 360581201860420382, 360581195440488747, 360581182868410883, 360581168670425102, 360581156405025636, 360581144141498467, 360581137153538356]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 12760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 12700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360384157284820339, 360384158194546964⟩, ⟨2516161874950746317, 2516169750391165773⟩, true⟩

def words07 : List Nat := [360581131827498889, 360581121422501989, 360581111019104365, 360581104450592545, 360581100997367579, 360581093042566767, 360581085088994054, 360581074087222682, 360581056993207553, 360581041586596351]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 12770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 12700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360474848504726290, 360474849415936390⟩, ⟨1357092777067551431, 1357100671474297541⟩, true⟩

def words08 : List Nat := [360581026182342870, 360581016871371282, 360581011001804857, 360581002089394927, 360580993178353214, 360580982696164606, 360580975320860739, 360580970532497520, 360580965744869588, 360580955801509049]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 12780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 12700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587510339846492, 360587511252542314⟩, ⟨(-84697499533938231), (-84689586117347121)⟩, true⟩

def words09 : List Nat := [360580947506242450, 360580945292174039, 360580943078406087, 360580941706712363, 360580934256112755, 360580921529093078, 360580908804029937, 360580899917313056, 360580894878463833, 360580895395490729]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 12790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 12700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 12700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk127
