import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk100

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360525029259002605, 360525029803013973⟩, ⟨562709426242510145, 562713113843161073⟩, true⟩

def state01 : KState := ⟨⟨360735446435996934, 360735446981150225⟩, ⟨(-1543118581693813492), (-1543114882668310304)⟩, true⟩

def words00 : List Nat := [360581296142756401, 360581301774148748, 360581306910194932, 360581312045235776, 360581312045347337, 360581307504851184, 360581293088817988, 360581288625725030, 360581289650085881, 360581305049008750]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 10000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 10000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360547361222368236, 360547361768672109⟩, ⟨340527286231850718, 340530996780481592⟩, true⟩

def words01 : List Nat := [360581314190514937, 360581323330208361, 360581329729729238, 360581341081844796, 360581349775595715, 360581358467630511, 360581359304507655, 360581359304628720, 360581350290021693, 360581346898091319]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 10010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 10000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360493978060207210, 360493978607651849⟩, ⟨875015957375590204, 875019679360464628⟩, true⟩

def words02 : List Nat := [360581343506799053, 360581341401426950, 360581329449046266, 360581311098047570, 360581292750688369, 360581271695523761, 360581255930347426, 360581245259303499, 360581234590374289, 360581218854846313]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 10020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 10000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360694557398705682, 360694557947296371⟩, ⟨(-1138569868401759654), (-1138566134916324768)⟩, true⟩

def words03 : List Nat := [360581210157882365, 360581200986389287, 360581191816688339, 360581188886653708, 360581181451064967, 360581165081069615, 360581148714312665, 360581143649342199, 360581154945685279, 360581166239805452]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 10030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 10000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360414805917107653, 360414806466853120⟩, ⟨1670723399412816791, 1670727144497868717⟩, true⟩

def words04 : List Nat := [360581172484421363, 360581172484542703, 360581168913874780, 360581165648639158, 360581162384022230, 360581150851056610, 360581129510211202, 360581101427921145, 360581073351197586, 360581047973768331]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 10040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 10000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360265934980599183, 360265935531489028⟩, ⟨3167858733570479042, 3167862490162413614⟩, true⟩

def words05 : List Nat := [360581031434069304, 360581015229814648, 360580999028769489, 360580977925597872, 360580955652658442, 360580930756996232, 360580905866249814, 360580887534435851, 360580863704160147, 360580832399298414]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 10050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 10000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360633869735216486, 360633870287254358⟩, ⟨(-535584506280121493), (-535580738133461265)⟩, true⟩

def words06 : List Nat := [360580801100632559, 360580779647531313, 360580764844585124, 360580754717382638, 360580744592183377, 360580724355644277, 360580704564687057, 360580694604244437, 360580684645745065, 360580689794936469]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 10060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 10000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360529215546970151, 360529216100169742⟩, ⟨518654456780042824, 518658236630953692⟩, true⟩

def words07 : List Nat := [360580689887288487, 360580689979634373, 360580689979734647, 360580695777576860, 360580695777679472, 360580695625363439, 360580695473063623, 360580690307108042, 360580675395258510, 360580670290311702]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 10070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 10000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360371023632027086, 360371024186373403⟩, ⟨2114002131084779914, 2114005922500616344⟩, true⟩

def words08 : List Nat := [360580665186334635, 360580662940430383, 360580653323769954, 360580638707061780, 360580624093232555, 360580606895402279, 360580595769784407, 360580579160457597, 360580562554410758, 360580539144004783]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 10080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 10000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360728682863894480, 360728683419391853⟩, ⟨(-1496708267194117450), (-1496704464158543626)⟩, true⟩

def words09 : List Nat := [360580518381547076, 360580507402417052, 360580496425427242, 360580495366235673, 360580495366348054, 360580487271175005, 360580479177582463, 360580480184771353, 360580494858457800, 360580509529266268]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 10090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 10000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 10000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk100
