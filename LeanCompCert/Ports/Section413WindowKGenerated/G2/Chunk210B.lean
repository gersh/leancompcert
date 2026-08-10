import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk210A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk210B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk210A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk210B
