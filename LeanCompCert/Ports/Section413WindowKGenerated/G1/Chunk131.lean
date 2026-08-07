import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk131

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362565030927727470, 362565033140863331⟩, ⟨(-1055330578992558222), (-1055310962457680342)⟩, true⟩

def state01 : KState := ⟨⟨362498321225179644, 362498323441853715⟩, ⟨(-181436650837990532), (-181416987935481930)⟩, true⟩

def words00 : List Nat := [371284486133318563, 371284486133710283, 371284486313096113, 371284489312315886, 371284494033688929, 371284494034080708, 371284491008170983, 371284487193754505, 371284485379778413, 371284486435680618]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 13100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 13100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362443464828339000, 362443467048551846⟩, ⟨538131865488444180, 538151574802342492⟩, true⟩

def words01 : List Nat := [371284489880446147, 371284493324846559, 371284496694659177, 371284496695051488, 371284493486438340, 371284491391414921, 371284490953648664, 371284490954047734, 371284487825207914, 371284484699070318]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 13110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 13100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362498304845240429, 362498307068964990⟩, ⟨(-181481437410494964), (-181461682004831850)⟩, true⟩

def words02 : List Nat := [371284484251422501, 371284484251858842, 371284486751469646, 371284489476635856, 371284490764688095, 371284490765080666, 371284484329875896, 371284483693860737, 371284486681503913, 371284487734412799]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 13120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 13100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362457078456654577, 362457080683960402⟩, ⟨360296507333833411, 360316309779626333⟩, true⟩

def words03 : List Nat := [371284488733306614, 371284489732181297, 371284494685625221, 371284497652892808, 371284501493016665, 371284505332710393, 371284508572580752, 371284508572973770, 371284504103048645, 371284502016515930]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 13130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 13100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362404768312547338, 362404770543354815⟩, ⟨1047905564977897170, 1047925413453642566⟩, true⟩

def words04 : List Nat := [371284501437822159, 371284501438215248, 371284495242499976, 371284488899652267, 371284482557618054, 371284476368061284, 371284468106887083, 371284465625315906, 371284463143995870, 371284460688864598]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 13140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 13100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362502346219617268, 362502348453992851⟩, ⟨(-235796378386556475), (-235776482972657471)⟩, true⟩

def words05 : List Nat := [371284454629505794, 371284454346831358, 371284456166160483, 371284456166553931, 371284450577717506, 371284444066905189, 371284437556921822, 371284435352543037, 371284432307417600, 371284433669176146]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 13150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 13100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362416479279453293, 362416481517377187⟩, ⟨894489137640513001, 894509079768778503⟩, true⟩

def words06 : List Nat := [371284434439956005, 371284434440349706, 371284427528544019, 371284426383159409, 371284425793281363, 371284425793675529, 371284420281333735, 371284412849179150, 371284405417990284, 371284401720852417]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 13160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 13100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362438563844288605, 362438566085756604⟩, ⟨603834614917211730, 603854603739469186⟩, true⟩

def words07 : List Nat := [371284397166008463, 371284397768028499, 371284398366627470, 371284398367028280, 371284394213611779, 371284390439249881, 371284388644744745, 371284388645141550, 371284385540795576, 371284382064796018]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 13170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 13100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491337421539025, 362491339666541389⟩, ⟨(-91783072318773915), (-91763036895416889)⟩, true⟩

def words08 : List Nat := [371284378589158001, 371284377326060658, 371284376181789951, 371284378484858057, 371284380011016482, 371284380011411684, 371284377090242704, 371284378504073127, 371284382650447413, 371284383178261849]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 13180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 13100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474526959937136, 362474529208537942⟩, ⟨130170585346414922, 130190668250870554⟩, true⟩

def words09 : List Nat := [371284383700924007, 371284384223644096, 371284389567727990, 371284392089036906, 371284394240611530, 371284396392000748, 371284398459069481, 371284398459464295, 371284392884702204, 371284392137950887]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 13190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 13100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 13100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk131
