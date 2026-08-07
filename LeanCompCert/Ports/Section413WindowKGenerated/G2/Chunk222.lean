import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk222

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

def state06 : KState := ⟨⟨360533713673622525, 360533716577145016⟩, ⟨1032245670960331803, 1032289401670350321⟩, true⟩

def words05 : List Nat := [360580109647666448, 360580108728036803, 360580107808441098, 360580105334471479, 360580103875340371, 360580101900145054, 360580099925096852, 360580096944368219, 360580092847159306, 360580090764102355]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 22250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 22200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360496302511534080, 360496305417768059⟩, ⟨1865105899193593484, 1865149690275036108⟩, true⟩

def words06 : List Nat := [360580088681132164, 360580088150032914, 360580085612203667, 360580081822238529, 360580078032564818, 360580073327117693, 360580069642383850, 360580065890377800, 360580062138677949, 360580057087739996]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 22260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 22200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360678199856533865, 360678202765485323⟩, ⟨(-2186719407589388689), (-2186675555976393471)⟩, true⟩

def words07 : List Nat := [360580053327402489, 360580051579249198, 360580050094594047, 360580051241472633, 360580051241742942, 360580050404948466, 360580050742282502, 360580053137233841, 360580057542746591, 360580061947928823]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 22270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 22200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360685114190926744, 360685117102627606⟩, ⟨(-2341101751574690258), (-2341057838691289796)⟩, true⟩

def words08 : List Nat := [360580064811580828, 360580067131496132, 360580071461584844, 360580075791371857, 360580079604926484, 360580083151579923, 360580084988797306, 360580086825884722, 360580089832730301, 360580094544703274]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 22280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 22200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360581987610056113, 360581990524470147⟩, ⟨(-41575804437695370), (-41531831063728534)⟩, true⟩

def words09 : List Nat := [360580101264892705, 360580107984534278, 360580113703304029, 360580118186314620, 360580121005297905, 360580123824099047, 360580126925726657, 360580128026445270, 360580128110222331, 360580128194033677]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 22290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 22200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 22200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk222
