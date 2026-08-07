import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk722

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582037547256064, 360582071227276817⟩, ⟨19223618086599009, 20866100506609015⟩, true⟩

def state01 : KState := ⟨⟨360575032149949832, 360575065839724000⟩, ⟨524942622831680198, 526585809496073628⟩, true⟩

def words00 : List Nat := [360582360228349815, 360582360101326270, 360582359917375701, 360582359880867994, 360582359844097115, 360582359674783714, 360582359366040636, 360582358947229967, 360582358528234709, 360582358261957709]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360542400569862069, 360542434269306600⟩, ⟨2881521042258449939, 2883164927267623691⟩, true⟩

def words01 : List Nat := [360582358252275042, 360582358343791687, 360582358344705079, 360582358340595183, 360582358144892158, 360582357775820622, 360582357406444703, 360582357196253765, 360582356794549373, 360582356242821799]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360607655484775725, 360607689193897178⟩, ⟨(-1831533948534046354), (-1829889364611067436)⟩, true⟩

def words02 : List Nat := [360582355690875689, 360582355330642855, 360582355066666522, 360582354994286409, 360582354921838853, 360582354686880729, 360582354647235833, 360582354723821584, 360582354991469741, 360582355343270563]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583061990290063, 360583095709189312⟩, ⟨(-55023170798725303), (-53377880577492291)⟩, true⟩

def words03 : List Nat := [360582355599374476, 360582355855583060, 360582356026471120, 360582356293586860, 360582356511810199, 360582356730194695, 360582356806710667, 360582356807738351, 360582356811534630, 360582356822953276]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574405697441628, 360574439425993844⟩, ⟨570305522257873948, 571951509858537806⟩, true⟩

def words04 : List Nat := [360582356890865941, 360582356891891941, 360582356849467959, 360582356681566994, 360582356513503517, 360582356297153642, 360582356176989666, 360582356053126213, 360582355929147551, 360582355709867319]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360611464728354725, 360611498466586071⟩, ⟨(-2107348255409985120), (-2105701568443182658)⟩, true⟩

def words05 : List Nat := [360582355682809193, 360582355765627855, 360582356039368749, 360582356396137684, 360582356589730216, 360582356783397102, 360582357061511747, 360582357436326793, 360582357840442025, 360582358244772878]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601117292504935, 360601151040532570⟩, ⟨(-1359754068949868793), (-1358106674057922147)⟩, true⟩

def words06 : List Nat := [360582358486619156, 360582358537368724, 360582358736573625, 360582358936073990, 360582359047073256, 360582359070187536, 360582359071108592, 360582358956475789, 360582358917106481, 360582359178318710]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360580461733533846, 360580495491212130⟩, ⟨133182948475871574, 134831040868781260⟩, true⟩

def words07 : List Nat := [360582359630305612, 360582360082476437, 360582360439128327, 360582360604769177, 360582360620027025, 360582360635542367, 360582360841864972, 360582360914045526, 360582360914969218, 360582360890228024]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588564520047044, 360588598287422118⟩, ⟨(-452496419651845786), (-450847626326297518)⟩, true⟩

def words08 : List Nat := [360582360869087921, 360582361020525694, 360582361230184059, 360582361440035191, 360582361478776566, 360582361479803066, 360582361492390810, 360582361594937391, 360582361633623302, 360582361720957050]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360577034973813620, 360577068750960332⟩, ⟨381004834680456653, 382654334445557597⟩, true⟩

def words09 : List Nat := [360582361721871523, 360582361713848755, 360582361705625971, 360582361778705133, 360582361779566016, 360582361774424670, 360582361769163241, 360582361645658015, 360582361414063645, 360582361342031502]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk722
