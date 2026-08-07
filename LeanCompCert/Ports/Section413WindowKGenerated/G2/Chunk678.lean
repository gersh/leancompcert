import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk678

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360563234356221628, 360563263908204882⟩, ⟨1326280175730026075, 1327633593106959055⟩, true⟩

def state01 : KState := ⟨⟨360582339229455662, 360582368790471576⟩, ⟨30920111728653052, 32274141565202292⟩, true⟩

def words00 : List Nat := [360582845236586632, 360582845171640435, 360582845172493824, 360582845044047669, 360582844915441319, 360582844696799482, 360582844693084862, 360582844800425752, 360582844801294013, 360582844740059620]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 67800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 67800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598920786390591, 360598950356443193⟩, ⟨(-1093660598993932017), (-1092305956334253617)⟩, true⟩

def words01 : List Nat := [360582844737860298, 360582844742958523, 360582844821131778, 360582844822090194, 360582844775828889, 360582844510648387, 360582844245275469, 360582844160891452, 360582844399150508, 360582844637619610]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 67810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 67800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585769240490126, 360585798819687606⟩, ⟨(-201857609134597311), (-200502346226609183)⟩, true⟩

def words02 : List Nat := [360582844705081996, 360582844706040158, 360582844556252650, 360582844401803919, 360582844247096056, 360582844037116809, 360582843794690625, 360582843412716005, 360582843030568492, 360582842909466224]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 67820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 67800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360551929042690974, 360551958630903737⟩, ⟨2093783093819483019, 2095138968281040229⟩, true⟩

def words03 : List Nat := [360582843070585817, 360582843231883762, 360582843283749455, 360582843284712388, 360582843274430088, 360582843209503404, 360582843144316338, 360582842965076189, 360582842619479047, 360582842165223918]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 67830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 67800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360571815993385312, 360571845590647483⟩, ⟨744598553810353445, 745955042228644573⟩, true⟩

def words04 : List Nat := [360582841710764792, 360582841432768375, 360582841309556759, 360582841357046098, 360582841357930019, 360582841220842405, 360582840866574203, 360582840469279640, 360582840071710200, 360582839769604427]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 67840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 67800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360572421360956838, 360572450967369482⟩, ⟨703519578251311376, 704876687572333176⟩, true⟩

def words05 : List Nat := [360582839608448096, 360582839277327190, 360582838946032499, 360582838848146685, 360582838848949352, 360582838757581523, 360582838666111818, 360582838466012545, 360582838338422131, 360582838186461324]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 67850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 67800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575552532084409, 360575582147517780⟩, ⟨490951132138636675, 492308853652948323⟩, true⟩

def words06 : List Nat := [360582838042506697, 360582838043465513, 360582837835718099, 360582837519368861, 360582837202884186, 360582836736856989, 360582836379886149, 360582836239982261, 360582836099983505, 360582835850975169]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 67860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 67800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360575149861253002, 360575179485744589⟩, ⟨518259081611620091, 519617417951714413⟩, true⟩

def words07 : List Nat := [360582835791212492, 360582835838622877, 360582835848937752, 360582835849896707, 360582835643442706, 360582835255144318, 360582834866673655, 360582834645951147, 360582834538862216, 360582834427081533]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 67870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 67800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575341579595849, 360575371213217978⟩, ⟨505095879079694548, 506454835246351492⟩, true⟩

def words08 : List Nat := [360582834315173981, 360582834008444623, 360582833484705156, 360582833178024483, 360582832871098817, 360582832509522131, 360582832239748420, 360582831836243607, 360582831432567702, 360582831145980482]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 67880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 67800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360555260476140209, 360555290118812386⟩, ⟨1868557816666263826, 1869917387284762540⟩, true⟩

def words09 : List Nat := [360582831143702911, 360582831251493414, 360582831252363120, 360582831181333203, 360582830949121108, 360582830612180671, 360582830274957255, 360582830076236074, 360582829807447036, 360582829402866654]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 67890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 67800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 67800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk678
