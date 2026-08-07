import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk908

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580489959083958, 360580544189622175⟩, ⟨129442100106701484, 132767247875750668⟩, true⟩

def state01 : KState := ⟨⟨360567110887337263, 360567165130374300⟩, ⟨1344237633274184326, 1347563915995811170⟩, true⟩

def words00 : List Nat := [360582006369061896, 360582006270217676, 360582006080999060, 360582006013329544, 360582005945298752, 360582005773848498, 360582005481161017, 360582005127870216, 360582004774335970, 360582004508372272]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360561001590158544, 360561055845563973⟩, ⟨1899026172842229905, 1902353578799272579⟩, true⟩

def words01 : List Nat := [360582004346041350, 360582004181258629, 360582004016336300, 360582003790831178, 360582003525062192, 360582003202626172, 360582002879801676, 360582002660608155, 360582002491697722, 360582002262419284]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576841282389344, 360576895550165978⟩, ⟨460430105498974484, 463758635069690168⟩, true⟩

def words02 : List Nat := [360582002032845355, 360582001924737062, 360582001949512189, 360582002023216493, 360582002024448665, 360582001983933316, 360582001822130986, 360582001632075773, 360582001441623444, 360582001337186453]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360568902404996335, 360568956685279618⟩, ⟨1181580960097462102, 1184910625710232930⟩, true⟩

def words03 : List Nat := [360582001282151916, 360582001133915611, 360582000985408260, 360582000990666086, 360582000991764434, 360582000968228174, 360582000944560286, 360582000860523775, 360582000757646697, 360582000615549436]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581894436968361, 360581948729609582⟩, ⟨1298288166504401, 4629076434136019⟩, true⟩

def words04 : List Nat := [360582000473019072, 360582000451775971, 360582000348501588, 360582000181169655, 360582000013621092, 360581999816061344, 360581999732968209, 360581999752717065, 360581999753893861, 360581999682569782]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360581886787108312, 360581941092151769⟩, ⟨1963927788254317, 5295842859022207⟩, true⟩

def words05 : List Nat := [360581999765184152, 360581999848742939, 360581999929238998, 360581999930551084, 360581999890222744, 360581999748326810, 360581999606188000, 360581999454592600, 360581999377147309, 360581999377897521]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 90850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 90800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360570056481147126, 360570110798673827⟩, ⟨1076840918018280131, 1080173967379826237⟩, true⟩

def words06 : List Nat := [360581999378425963, 360581999310698905, 360581999146747630, 360581999104176388, 360581999061247515, 360581998947851094, 360581998713396371, 360581998385955115, 360581998058269641, 360581997823735782]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 90860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 90800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360550006592625196, 360550060922500003⟩, ⟨2898910671461612481, 2902244842958948867⟩, true⟩

def words07 : List Nat := [360581997693991783, 360581997580576896, 360581997467033298, 360581997275397251, 360581997086481833, 360581996864965926, 360581996643071654, 360581996474550409, 360581996184985978, 360581995834944534]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 90870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 90800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571789779210038, 360571844121495941⟩, ⟨919107221012495771, 922442520488423721⟩, true⟩

def words08 : List Nat := [360581995484631325, 360581995132035051, 360581994887780404, 360581994680314294, 360581994472751060, 360581994163917634, 360581993790077607, 360581993537563009, 360581993284643301, 360581993120511107]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 90880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 90800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554846570904506, 360554900925702350⟩, ⟨2459166772405965471, 2462503209151730857⟩, true⟩

def words09 : List Nat := [360581993010030330, 360581992839274509, 360581992668277048, 360581992516158636, 360581992424465233, 360581992243015732, 360581992061416516, 360581991804343909, 360581991466539641, 360581991170027452]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 90800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 90800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk908
