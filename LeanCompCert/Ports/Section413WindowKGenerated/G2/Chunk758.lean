import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk758

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360612309071128776, 360612346336788258⟩, ⟨(-2286510920398138171), (-2284603044889677237)⟩, true⟩

def state01 : KState := ⟨⟨360582170155773589, 360582207431733878⟩, ⟨(-1972256456270150), (-63600097196304)⟩, true⟩

def words00 : List Nat := [360582207118750661, 360582207254212466, 360582207274214388, 360582207294510418, 360582207295414291, 360582207271604956, 360582207154437637, 360582206949486669, 360582206744333504, 360582206592804209]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 75800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 75800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360546564292909963, 360546601579037968⟩, ⟨2697550034256453461, 2699459461479949329⟩, true⟩

def words01 : List Nat := [360582206713312296, 360582206834030956, 360582206844278187, 360582206845358122, 360582206681801067, 360582206439801416, 360582206197488569, 360582205951162882, 360582205575087527, 360582205106622774]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 75810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 75800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360557596146937075, 360557633443256310⟩, ⟨1861105602254365669, 1863015802227506097⟩, true⟩

def words02 : List Nat := [360582204637922665, 360582204343336508, 360582204135700593, 360582203907201406, 360582203678616137, 360582203298668175, 360582202815661074, 360582202473688829, 360582202131414616, 360582201764530575]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 75820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 75800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565567385332607, 360565604691952296⟩, ⟨1256571386295715246, 1258482367403850078⟩, true⟩

def words03 : List Nat := [360582201441523527, 360582200969420613, 360582200497123410, 360582200198909821, 360582200034461105, 360582199791183953, 360582199547798222, 360582199182735967, 360582198822596611, 360582198605024605]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 75830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 75800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570107541695836, 360570144858486379⟩, ⟨912199245306607766, 914110997822061056⟩, true⟩

def words04 : List Nat := [360582198387099586, 360582198306895031, 360582198174805221, 360582197945522128, 360582197716090927, 360582197328747299, 360582197028223907, 360582196858249384, 360582196688159445, 360582196420751667]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 75840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 75800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360600346844364511, 360600384171375588⟩, ⟨(-1381573247940141211), (-1379660720149098031)⟩, true⟩

def words05 : List Nat := [360582196262740893, 360582196235096799, 360582196351874667, 360582196536268062, 360582196572756367, 360582196609330169, 360582196751771881, 360582196996848083, 360582197237483876, 360582197478342949]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360604805588022310, 360604842925334851⟩, ⟨(-1719958600552128065), (-1718045291241799539)⟩, true⟩

def words06 : List Nat := [360582197631341905, 360582197653979490, 360582197814573180, 360582197975480729, 360582198092192873, 360582198214159473, 360582198215131299, 360582198196277114, 360582198330821316, 360582198630528644]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360584266845617610, 360584304193120577⟩, ⟨(-161573269553748267), (-159659187043767141)⟩, true⟩

def words07 : List Nat := [360582198988765288, 360582199347197006, 360582199571554207, 360582199681693830, 360582199742952297, 360582199804494353, 360582199945801963, 360582200062238339, 360582200090940366, 360582200119807841]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592280787173043, 360592318144877622⟩, ⟨(-769663931549224336), (-767749074889486726)⟩, true⟩

def words08 : List Nat := [360582200193421684, 360582200354370291, 360582200688481534, 360582201022791096, 360582201209355354, 360582201322207198, 360582201385651637, 360582201449411108, 360582201539793621, 360582201674217208]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588631347605238, 360588668715609613⟩, ⟨(-492692995770305736), (-490777357411274292)⟩, true⟩

def words09 : List Nat := [360582201699656704, 360582201725212907, 360582201843914254, 360582202103482279, 360582202286343869, 360582202469376816, 360582202562816844, 360582202563898254, 360582202609523968, 360582202695960185]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk758
