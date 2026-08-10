import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk574A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk574B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk574A

def state06 : KState := ⟨⟨360554796547235967, 360554817494693009⟩, ⟨1558003136952730902, 1558816331939694054⟩, true⟩

def words05 : List Nat := [360581947799678716, 360581947935190480, 360581947935909240, 360581947844083878, 360581947613680873, 360581947306320002, 360581946998708510, 360581946994187400, 360581946687402923, 360581946216098156]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 57450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 57400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591119204622085, 360591140159648360⟩, ⟨(-529341702291110926), (-528528072337808682)⟩, true⟩

def words06 : List Nat := [360581945744622483, 360581945447903693, 360581945341698959, 360581945226885668, 360581945112015418, 360581944736286961, 360581944162312734, 360581943891413218, 360581943620288123, 360581943728886101]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 57460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 57400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360572664279650649, 360572685242310097⟩, ⟨531345371007908838, 532159439676698832⟩, true⟩

def words07 : List Nat := [360581943736909489, 360581943745020103, 360581943841882756, 360581944117900740, 360581944160682533, 360581944203586873, 360581944204316660, 360581943966181102, 360581943569475327, 360581943409319087]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 57470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 57400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360589447832477445, 360589468802683476⟩, ⟨(-433495538413809206), (-432681035929436150)⟩, true⟩

def words08 : List Nat := [360581943291439565, 360581943292241643, 360581943161449236, 360581942876953673, 360581942592323315, 360581942230887111, 360581942342700964, 360581942550361006, 360581942605368448, 360581942737109223]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 57480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 57400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360613148525669658, 360613169503458724⟩, ⟨(-1796219384469738176), (-1795404445999809154)⟩, true⟩

def words09 : List Nat := [360581942781469435, 360581942826060012, 360581943172916004, 360581943580107120, 360581943731338015, 360581943882626253, 360581944078794917, 360581944533784227, 360581945077478637, 360581945621334939]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 57490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 57400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 57400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk574B
