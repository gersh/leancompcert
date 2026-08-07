import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk040

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨359908601615951922, 359908601694962903⟩, ⟨2639266091865636113, 2639266306539655711⟩, true⟩

def state01 : KState := ⟨⟨360532656931491033, 360532657010919171⟩, ⟨141007272288409067, 141007488633130621⟩, true⟩

def words00 : List Nat := [360568253358717764, 360568150206770501, 360568097891664549, 360568102570070050, 360568102570111153, 360568053290518396, 360567943344010384, 360567895008536238, 360567846697163023, 360567820973171823]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 4000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 4000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360697755879392985, 360697755959243852⟩, ⟨(-522875502519240047), (-522875284477257149)⟩, true⟩

def words01 : List Nat := [360567812206330320, 360567754639336341, 360567700985490608, 360567739665425060, 360567739665462507, 360567734917010468, 360567730170918077, 360567684054344423, 360567687480467783, 360567719827814542]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 4010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 4000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360788123204781340, 360788123285050830⟩, ⟨(-887394476592020438), (-887394256865065094)⟩, true⟩

def words02 : List Nat := [360567813415176728, 360567846735948313, 360567846735988339, 360567845854327338, 360567844973098048, 360567792727875201, 360567851247648442, 360567911030384291, 360567926198933890, 360567980824900728]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 4020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 4000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360691044601474445, 360691044682165198⟩, ⟨(-495624928158674247), (-495624706731847785)⟩, true⟩

def words03 : List Nat := [360568062045032919, 360568143224901277, 360568253253214382, 360568303216632048, 360568303216673168, 360568300313452351, 360568300865346191, 360568334925525661, 360568365299264639, 360568395657980133]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 4030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 4000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360847908997068395, 360847909078185458⟩, ⟨(-1132629365106648380), (-1132629141955433662)⟩, true⟩

def words04 : List Nat := [360568395658020333, 360568394653903424, 360568369183272103, 360568358194127871, 360568347210405559, 360568319426673726, 360568316602644652, 360568273444837533, 360568247561601910, 360568316596833833]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 4040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 4000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360389053172230919, 360389053253770848⟩, ⟨729454083143540905, 729454308009525339⟩, true⟩

def words05 : List Nat := [360568445936961637, 360568575213273439, 360568657482110625, 360568680333011771, 360568686515829511, 360568692695611086, 360568759057608057, 360568766066693514, 360568766066734190, 360568721802541668]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 4050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 4000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360628834916344219, 360628834998308535⟩, ⟨(-245364667440691720), (-245364440849566894)⟩, true⟩

def words06 : List Nat := [360568677560138184, 360568677408955639, 360568708089430039, 360568738754817826, 360568738754859315, 360568717671105458, 360568677055508034, 360568629435078488, 360568581838042309, 360568563703577618]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 4060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 4000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360697825459221785, 360697825541615080⟩, ⟨(-526489930139017980), (-526489701799773364)⟩, true⟩

def words07 : List Nat := [360568563703617896, 360568535754409483, 360568539595750272, 360568622514030859, 360568685961222258, 360568749377296396, 360568780243067234, 360568780243112320, 360568783947985377, 360568815568128246]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 4070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 4000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360400167986931809, 360400168069751637⟩, ⟨688388971308416064, 688389201390072664⟩, true⟩

def words08 : List Nat := [360568815568165737, 360568811294680131, 360568795236662514, 360568748457658167, 360568701701549535, 360568620783340546, 360568572991975114, 360568554581181580, 360568536179387586, 360568478387939919]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 4080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 4000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨361013182824771435, 361013182908019437⟩, ⟨(-1821990976693708304), (-1821990744858714550)⟩, true⟩

def words09 : List Nat := [360568455374137734, 360568473493098858, 360568550823742755, 360568609356976524, 360568613346421723, 360568617333921698, 360568637118802980, 360568686507628535, 360568794921421580, 360568903282352840]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 4090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 4000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 4000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk040
