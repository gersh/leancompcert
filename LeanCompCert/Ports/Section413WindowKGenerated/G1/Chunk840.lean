import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk840

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478696773972461, 362478802977660902⟩, ⟨542015375046298731, 548039123554262285⟩, true⟩

def state01 : KState := ⟨⟨362467683504076089, 362467789733694024⟩, ⟨1467218499308186201, 1473244426030852433⟩, true⟩

def words00 : List Nat := [371285327227985375, 371285327230900690, 371285327110005065, 371285326990045017, 371285326868997815, 371285326783433332, 371285326644001222, 371285326523071755, 371285326401135347, 371285326270130530]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 84000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 84000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492971681179996, 362493077937125412⟩, ⟨(-657346995295322812), (-651318856666876540)⟩, true⟩

def words01 : List Nat := [371285326063366703, 371285325999724069, 371285325974397447, 371285325977372035, 371285325928352122, 371285325857705215, 371285325853600770, 371285325889412273, 371285325983666414, 371285326079177199]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 84010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 84000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477209750655784, 362477316032924737⟩, ⟨667026434455456957, 673056784923725485⟩, true⟩

def words02 : List Nat := [371285326146215866, 371285326149133145, 371285326078813276, 371285326110111554, 371285326181841876, 371285326184758095, 371285326067854168, 371285325939054724, 371285325809056438, 371285325753083297]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 84020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 84000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362462201834594903, 362462308143135960⟩, ⟨1928258993081745916, 1934291551327083656⟩, true⟩

def words03 : List Nat := [371285325659747912, 371285325656636851, 371285325652503833, 371285325648998393, 371285325455935502, 371285325271252719, 371285325085096582, 371285325004221508, 371285324733906850, 371285324463356416]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 84030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 84000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472985494708193, 362473091829395160⟩, ⟨1022002251443018086, 1028037007119010726⟩, true⟩

def words04 : List Nat := [371285324191465754, 371285324039745380, 371285323852215718, 371285323791108577, 371285323729131785, 371285323654785153, 371285323390836442, 371285323269954650, 371285323147548067, 371285323084685095]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 84040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 84000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362483082707850180, 362483189069096019⟩, ⟨173268438889932055, 179305426973296595⟩, true⟩

def words05 : List Nat := [371285322941381222, 371285322773954739, 371285322605371201, 371285322579506695, 371285322481779239, 371285322428502169, 371285322374152072, 371285322320512916, 371285322155655520, 371285322133894655]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481774526922556, 362481880914177865⟩, ⟨283257199456039933, 289296374032067423⟩, true⟩

def words06 : List Nat := [371285322226575776, 371285322229512897, 371285322220917788, 371285322185921602, 371285322149774533, 371285322102200749, 371285322002692045, 371285322025808826, 371285322047943529, 371285322051016596]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485872696939772, 362485979110581959⟩, ⟨(-61318003019584817), (-55276609966271361)⟩, true⟩

def words07 : List Nat := [371285322027734386, 371285322046914075, 371285322137195891, 371285322140113820, 371285322056566616, 371285321948046037, 371285321838401315, 371285321788493958, 371285321678506138, 371285321689643028]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479484825838556, 362479591265804640⟩, ⟨475771079396928347, 481814685894791587⟩, true⟩

def words08 : List Nat := [371285321699586069, 371285321702512013, 371285321567677930, 371285321554641609, 371285321555053141, 371285321557971210, 371285321386648635, 371285321216305619, 371285321044748102, 371285321015904472]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362465966205940329, 362466072672205108⟩, ⟨1612640465867729501, 1618686283954565683⟩, true⟩

def words09 : List Nat := [371285320949781599, 371285320919717850, 371285320888695601, 371285320858364544, 371285320680733863, 371285320508643207, 371285320334975349, 371285320256211352, 371285320059331473, 371285319833726566]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk840
