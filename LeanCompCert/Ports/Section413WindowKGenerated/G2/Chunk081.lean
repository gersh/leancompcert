import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk081

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360533951501547717, 360533951850873986⟩, ⟨380324018758499760, 380325937365107636⟩, true⟩

def state01 : KState := ⟨⟨360456722873672705, 360456723223901207⟩, ⟨1006322303923710007, 1006324229843005305⟩, true⟩

def words00 : List Nat := [360580909182424738, 360580909182520599, 360580903401798141, 360580887459893723, 360580871521907625, 360580851766455800, 360580843753219727, 360580835405716000, 360580827060261576, 360580807592562491]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 8100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 8100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360573146870761501, 360573147221897511⟩, ⟨61040954027070269, 61042887310717969⟩, true⟩

def words01 : List Nat := [360580792294357816, 360580792068787681, 360580791843246474, 360580785010585357, 360580763131427940, 360580728040099630, 360580692957399490, 360580672939072132, 360580665744682342, 360580664818856960]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 8110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 8100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360496028741988778, 360496029094039162⟩, ⟨687090142524247863, 687092083237162769⟩, true⟩

def words02 : List Nat := [360580663893244103, 360580655353801779, 360580639544635508, 360580638770225666, 360580637995981807, 360580629059894650, 360580616200004979, 360580590896943761, 360580565600090191, 360580542265409047]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 8120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 8100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360474035216244619, 360474035569200846⟩, ⟨866378516437171297, 866380464519150697⟩, true⟩

def words03 : List Nat := [360580531871541427, 360580530491544321, 360580529111875840, 360580520154565513, 360580512955859290, 360580501971916740, 360580490990645251, 360580489120512819, 360580483592754504, 360580470515701971]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 8130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 8100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592426385661546, 360592426739527276⟩, ⟨(-98160684304548375), (-98158728814737937)⟩, true⟩

def words04 : List Nat := [360580457441841175, 360580443815144302, 360580442659509913, 360580444437937402, 360580444438026868, 360580433583754873, 360580407805635087, 360580396954017283, 360580386105033267, 360580384201333835]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 8140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 8100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360416284958489700, 360416285313274023⟩, ⟨1338273278097510476, 1338275241078497140⟩, true⟩

def words05 : List Nat := [360580384201420804, 360580372864139531, 360580361529621155, 360580363180396503, 360580363180478724, 360580357280936476, 360580351382830185, 360580338001257074, 360580309732955444, 360580289632033643]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 8150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 8100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360630463041925515, 360630463397621208⟩, ⟨(-410186424792934382), (-410184454370575778)⟩, true⟩

def words06 : List Nat := [360580269536006227, 360580268045034326, 360580268045121140, 360580264054507154, 360580260064854703, 360580246767861801, 360580250392366536, 360580259625316970, 360580259625404536, 360580263366490309]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 8160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 8100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360761040030065797, 360761040386674947⟩, ⟨(-1477825002213203565), (-1477823024323335765)⟩, true⟩

def words07 : List Nat := [360580284345465804, 360580305319336474, 360580328302066993, 360580343938999641, 360580347283759339, 360580350627710188, 360580350627789233, 360580355336450615, 360580377425166037, 360580399508503167]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 8170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 8100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360505865044012788, 360505865401546740⟩, ⟨609609310761740719, 609611296220863159⟩, true⟩

def words08 : List Nat := [360580413103645324, 360580413103742231, 360580411881427060, 360580409229955344, 360580406579105472, 360580400191140453, 360580378997780078, 360580350364599096, 360580321738392831, 360580299015248922]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 8180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 8100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360257773651188147, 360257774009634543⟩, ⟨2643671203167499467, 2643673196104286843⟩, true⟩

def words09 : List Nat := [360580295604520894, 360580301279669371, 360580301279755717, 360580299530172213, 360580293830684343, 360580277474527870, 360580261122335473, 360580244191921033, 360580212501557943, 360580173179891164]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 8190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 8100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 8100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk081
