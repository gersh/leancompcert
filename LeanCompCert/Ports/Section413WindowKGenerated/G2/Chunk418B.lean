import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk418A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk418B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk418A

def state06 : KState := ⟨⟨360554665528382562, 360554676361741820⟩, ⟨1163384356504513584, 1163690833393869958⟩, true⟩

def words05 : List Nat := [360582475128917850, 360582476080209020, 360582476586053109, 360582476905832740, 360582476906312489, 360582476853008413, 360582476990621622, 360582476991191029, 360582476615167596, 360582475951646117]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360611062252802565, 360611073091530152⟩, ⟨(-1197650872246197763), (-1197344170611127887)⟩, true⟩

def words06 : List Nat := [360582475288013985, 360582474958409060, 360582475435437507, 360582475958972460, 360582475999426772, 360582476000000105, 360582475996703007, 360582475979609463, 360582476382781653, 360582477066343003]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592178022267640, 360592188866419604⟩, ⟨(-406895437034988976), (-406588508254675780)⟩, true⟩

def words07 : List Nat := [360582477344577006, 360582477622858497, 360582478066181744, 360582478955894612, 360582479639141029, 360582480322448737, 360582480552975442, 360582480553545096, 360582480448667707, 360582480681126639]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360589011641544387, 360589022491070467⟩, ⟨(-274449743238418868), (-274142589363500368)⟩, true⟩

def words08 : List Nat := [360582480761737920, 360582480762307852, 360582480491307330, 360582479850764265, 360582479210158661, 360582478424135343, 360582478142951328, 360582478287113721, 360582478287621405, 360582478302835202]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360614042699264771, 360614053554166042⟩, ⟨(-1323082439659801621), (-1322775060591498665)⟩, true⟩

def words09 : List Nat := [360582478889038921, 360582479475381510, 360582480630139257, 360582481218180615, 360582481305834952, 360582481393514284, 360582482049609041, 360582482989119962, 360582483743060214, 360582484497088849]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk418B
