import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk104

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362541313376504797, 362541314743056149⟩, ⟨(-588405236025994993), (-588395614233883623)⟩, true⟩

def state01 : KState := ⟨⟨362501239938956482, 362501241308264700⟩, ⟨(-171483275152403422), (-171473624674564956)⟩, true⟩

def words00 : List Nat := [371284749026076374, 371284749026386903, 371284751785204856, 371284756755805553, 371284764431327971, 371284764785884760, 371284765053517765, 371284765321204155, 371284769297861818, 371284770880383175]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 10400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 10400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362399577827989456, 362399579200048636⟩, ⟨887815218522203730, 887824897651502952⟩, true⟩

def words01 : List Nat := [371284779040612726, 371284787199395945, 371284795056276657, 371284795056582495, 371284793165972912, 371284793579557728, 371284798571423498, 371284798571729303, 371284791302372170, 371284783124967207]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 10410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 10400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362497342616846378, 362497343991648286⟩, ⟨(-131493800695333837), (-131484092972627143)⟩, true⟩

def words02 : List Nat := [371284774949000503, 371284772421654893, 371284765410169228, 371284762116916752, 371284758824199285, 371284754101860975, 371284740787668045, 371284736676488290, 371284737654511982, 371284738863379412]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 10420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 10400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485141342251561, 362485142719849376⟩, ⟨(-3832530448875263), (-3822793550940223)⟩, true⟩

def words03 : List Nat := [371284739301243371, 371284739739127542, 371284749369197624, 371284755244406388, 371284763843623987, 371284772441307465, 371284779053964484, 371284779054271797, 371284776551499966, 371284776586954928]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 10430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 10400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484528954395333, 362484530334725494⟩, ⟨2622177123953266, 2631942561796460⟩, true⟩

def words04 : List Nat := [371284784357102438, 371284784357409516, 371284782543393533, 371284780060525394, 371284777822925264, 371284777823262815, 371284776520191533, 371284779503345115, 371284782194937303, 371284782195257724]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 10440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 10400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362619101102744961, 362619102485848215⟩, ⟨(-1404586492147915589), (-1404576697716973055)⟩, true⟩

def words05 : List Nat := [371284785867861318, 371284789564009026, 371284802414176173, 371284803086851865, 371284803087090419, 371284800741066690, 371284805197359006, 371284808891482230, 371284821730466937, 371284834567129453]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 10450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 10400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362463093475522945, 362463094861396206⟩, ⟨227812329148993987, 227822152568515573⟩, true⟩

def words06 : List Nat := [371284845761170593, 371284845761477813, 371284852967751739, 371284861139932310, 371284868483397466, 371284868483704823, 371284863675683812, 371284858904060071, 371284854378961137, 371284854379311060]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 10460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 10400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362434724886032710, 362434726274684306⟩, ⟨525251651415854993, 525261503938451677⟩, true⟩

def words07 : List Nat := [371284857202675274, 371284862103313327, 371284866929082448, 371284866929390042, 371284859624676474, 371284854886093374, 371284854521775073, 371284854522084332, 371284851429783296, 371284846647197518]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 10470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 10400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362510425788321347, 362510427179725639⟩, ⟨(-268276124293400464), (-268266242908397852)⟩, true⟩

def words08 : List Nat := [371284844078341638, 371284844078680240, 371284844022407742, 371284846250606261, 371284846854929347, 371284846855242450, 371284842908418546, 371284845482280508, 371284853657680988, 371284856095662309]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 10480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 10400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362541115429370034, 362541116823582522⟩, ⟨(-590400963832490203), (-590391052975622683)⟩, true⟩

def words09 : List Nat := [371284858446836660, 371284860797662338, 371284866857509543, 371284869996599330, 371284875846082711, 371284881694573054, 371284887465092796, 371284887465401117, 371284889103867815, 371284894458762446]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 10490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 10400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 10400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk104
