import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk210

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360460713729112674, 360460716299897477⟩, ⟨2521605170202136481, 2521641701559347847⟩, true⟩

def state01 : KState := ⟨⟨360450931227250706, 360450933800579174⟩, ⟨2727020930877605369, 2727057515664674447⟩, true⟩

def words00 : List Nat := [360580788758644821, 360580785296613025, 360580779576020762, 360580772730101186, 360580765884789400, 360580758470165710, 360580752213400641, 360580745901480384, 360580739590130301, 360580731873671258]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 21000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 21000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360645971622152532, 360645974198030382⟩, ⟨(-1371812115909983792), (-1371775477547706450)⟩, true⟩

def words01 : List Nat := [360580725696265382, 360580721772113728, 360580717848256027, 360580716177201985, 360580715414857376, 360580712775871804, 360580710137085603, 360580710603757099, 360580713708809174, 360580716813626800]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 21010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 21000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585270043152971, 360585272621610107⟩, ⟨(-95863294296583021), (-95826601705054535)⟩, true⟩

def words02 : List Nat := [360580717782588421, 360580717782859307, 360580720030612058, 360580722279904109, 360580723540529076, 360580723540799611, 360580722546602110, 360580720103281998, 360580717660138637, 360580716176281542]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 21020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 21000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360536150900631420, 360536153481635087⟩, ⟨937576544011014226, 937613290169091424⟩, true⟩

def words03 : List Nat := [360580718642477786, 360580721108492970, 360580721977708688, 360580722248740256, 360580722248970654, 360580720921771544, 360580719963748444, 360580719964019203, 360580718968791153, 360580716850939702]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 21030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 21000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360562597122419878, 360562599705983339⟩, ⟨381253987498875177, 381290787527585309⟩, true⟩

def words04 : List Nat := [360580714733228619, 360580715234156018, 360580716712394333, 360580718190542451, 360580718190792357, 360580717530459929, 360580716171362559, 360580715479522601, 360580714787673379, 360580713282587975]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 21040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 21000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360568032835684647, 360568035421830290⟩, ⟨266799277374823985, 266836131770929481⟩, true⟩

def words05 : List Nat := [360580712422369907, 360580710410301157, 360580708398371437, 360580708699190920, 360580709222185848, 360580709745179913, 360580709745421289, 360580709148797508, 360580706304834125, 360580705703490828]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 21050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 21000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575445340137524, 360575447928838267⟩, ⟨110408698033000191, 110445606252443803⟩, true⟩

def words06 : List Nat := [360580706742613284, 360580706742884331, 360580706136557987, 360580703429127822, 360580700721912112, 360580696500297547, 360580693424037864, 360580692589136462, 360580691754286521, 360580689770615792]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 21060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 21000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604207554861660, 360604210146121799⟩, ⟨(-495881093215793934), (-495844131057115232)⟩, true⟩

def words07 : List Nat := [360580690252987879, 360580690984139576, 360580692383229699, 360580692604924848, 360580692605175101, 360580690949581920, 360580689294096102, 360580687582303913, 360580688128237867, 360580689244311776]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 21070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 21000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601741920087349, 360601744513930542⟩, ⟨(-444345666167202871), (-444308649545095723)⟩, true⟩

def words08 : List Nat := [360580689244553458, 360580689244172048, 360580687777132188, 360580687480182514, 360580687183184560, 360580686322693339, 360580684860492873, 360580681577442209, 360580678294651166, 360580678246349816]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 21080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 21000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360517215336703441, 360517217933106992⟩, ⟨1338611439758650837, 1338648510391577019⟩, true⟩

def words09 : List Nat := [360580678385163705, 360580678524012225, 360580678524254092, 360580677333016475, 360580674705884832, 360580671516653425, 360580668327643167, 360580665525633455, 360580663997112673, 360580660990471522]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 21090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 21000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 21000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk210
