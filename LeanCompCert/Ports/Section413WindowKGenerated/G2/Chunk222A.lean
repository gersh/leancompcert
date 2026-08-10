import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk222A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360640404697540692, 360640407584735707⟩, ⟨(-1339889347822979345), (-1339845980072762235)⟩, true⟩

def state01 : KState := ⟨⟨360659540595977750, 360659543485875688⟩, ⟨(-1764743247122163007), (-1764699819353165719)⟩, true⟩

def words00 : List Nat := [360580061303112558, 360580065078622941, 360580067843364421, 360580070607892213, 360580072851944103, 360580076114380964, 360580080680974582, 360580085247211744, 360580088293351882, 360580091870939253]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 22200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 22200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360676359347872615, 360676362240487488⟩, ⟨(-2138598215348148022), (-2138554727222723716)⟩, true⟩

def words01 : List Nat := [360580094692154629, 360580097513198177, 360580101662537800, 360580104811252009, 360580106229009131, 360580107646661218, 360580109654627958, 360580113321136678, 360580117653004423, 360580121984548389]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 22210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 22200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360637859700630307, 360637862595982237⟩, ⟨(-1283315097310620571), (-1283271548354735915)⟩, true⟩

def words02 : List Nat := [360580125265705941, 360580127474434121, 360580131046185593, 360580134617699409, 360580136717207807, 360580136804035100, 360580136804291414, 360580135723212744, 360580135580429038, 360580138177451594]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 22220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 22200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360491459221488103, 360491462119550275⟩, ⟨1971990607963765484, 1972034217182118158⟩, true⟩

def words03 : List Nat := [360580140253799860, 360580142330019445, 360580143384102464, 360580143384390086, 360580142426912301, 360580140951932679, 360580139477001224, 360580139098896361, 360580136709710067, 360580132722840838]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 22230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 22200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582324085627058, 360582326986405595⟩, ⟨(-49381679634445998), (-49338009990895306)⟩, true⟩

def words04 : List Nat := [360580128736265685, 360580125648361318, 360580124133390975, 360580122178202782, 360580120223167802, 360580116543354866, 360580113069553588, 360580111612286141, 360580110155063157, 360580109647410005]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 22240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 22200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk222A
