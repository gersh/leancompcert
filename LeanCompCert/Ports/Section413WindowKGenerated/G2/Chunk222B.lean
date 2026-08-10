import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk222A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk222B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk222A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk222B
