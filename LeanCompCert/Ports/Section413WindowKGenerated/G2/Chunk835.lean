import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk835

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588789735139819, 360588835299817973⟩, ⟨(-536549375361945931), (-533979932483093117)⟩, true⟩

def state01 : KState := ⟨⟨360599326552753714, 360599372128750939⟩, ⟨(-1416477683173479683), (-1413907295096161963)⟩, true⟩

def words00 : List Nat := [360582440507027762, 360582440679599579, 360582440821146420, 360582440962905710, 360582440988031355, 360582440989229796, 360582440975989310, 360582441028786194, 360582441133654944, 360582441337656399]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587697376933901, 360587742964348073⟩, ⟨(-445248779072469594), (-442677437510164698)⟩, true⟩

def words01 : List Nat := [360582441469042794, 360582441600559651, 360582441799391385, 360582442079357633, 360582442323017380, 360582442566866823, 360582442675829267, 360582442677027459, 360582442706292012, 360582442771133072]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575986868848365, 360576032467543266⟩, ⟨532817969876821745, 535390253662974857⟩, true⟩

def words02 : List Nat := [360582442885432717, 360582442886630934, 360582442857998930, 360582442720437157, 360582442582665635, 360582442364021392, 360582442216656470, 360582442176449398, 360582442136122303, 360582442024033904]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360604901627582244, 360604947237609826⟩, ⟨(-1882656071384993361), (-1880082840926143627)⟩, true⟩

def words03 : List Nat := [360582441948286808, 360582441869121376, 360582441818644891, 360582441826933717, 360582441828038947, 360582441714316452, 360582441628620487, 360582441784761468, 360582442055127570, 360582442325759045]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579631873912548, 360579677495341248⟩, ⟨228418791408349620, 230992974372919550⟩, true⟩

def words04 : List Nat := [360582442524438377, 360582442580290008, 360582442699062101, 360582442818181537, 360582442819209986, 360582442807722092, 360582442713039993, 360582442546616291, 360582442379968306, 360582442222742480]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360553358925661159, 360553404558394614⟩, ⟨2423680824400583484, 2426255951934198598⟩, true⟩

def words05 : List Nat := [360582442200442929, 360582442211479401, 360582442212547242, 360582442151815424, 360582441947979463, 360582441659977444, 360582441371608931, 360582441226575700, 360582440997895359, 360582440651644186]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591292490217828, 360591338134262509⟩, ⟨(-746211074015869342), (-743635001260584792)⟩, true⟩

def words06 : List Nat := [360582440305129433, 360582440102063626, 360582440012124850, 360582440039417351, 360582440040534366, 360582439946094174, 360582439889155348, 360582439815335284, 360582439784316361, 360582439892034218]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594463817777644, 360594509473259398⟩, ⟨(-1011318421265614662), (-1008741392658235542)⟩, true⟩

def words07 : List Nat := [360582439919510061, 360582439947119245, 360582439970780974, 360582440066965900, 360582440125293230, 360582440183814548, 360582440184887838, 360582440154531267, 360582440299904875, 360582440445697414]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580121040847811, 360580166707616761⟩, ⟨187506242418809368, 190084214466719448⟩, true⟩

def words08 : List Nat := [360582440603942937, 360582440719720433, 360582440740046301, 360582440760491881, 360582440761495480, 360582440756981245, 360582440787104432, 360582440817439790, 360582440818518405, 360582440714249932]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617587496036863, 360617633174122143⟩, ⟨(-2944504703626984696), (-2941925785591009350)⟩, true⟩

def words09 : List Nat := [360582440803807766, 360582440920933270, 360582441157982869, 360582441402588403, 360582441525320219, 360582441648142344, 360582441913709040, 360582442251126366, 360582442673040356, 360582443095228458]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk835
