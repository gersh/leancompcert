import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk418

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360530181825689547, 360530192626741407⟩, ⟨2185276285655058605, 2185581411128186481⟩, true⟩

def state01 : KState := ⟨⟨360582147141558793, 360582157947970609⟩, ⟨12849645801775222, 13154995347975730⟩, true⟩

def words00 : List Nat := [360582478012984395, 360582477333882001, 360582476939436339, 360582476739082166, 360582476538688349, 360582475847873105, 360582474588051294, 360582473730293712, 360582472872407678, 360582472585505840]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 41800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 41800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589870446719497, 360589881258553750⟩, ⟨(-310123823449562424), (-309818247165715166)⟩, true⟩

def words01 : List Nat := [360582472578499337, 360582472049775189, 360582471562441352, 360582471995987851, 360582472283283304, 360582472570657741, 360582472571164536, 360582472705177188, 360582472882791838, 360582473060587042]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 41810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 41800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592157185188721, 360592168002374605⟩, ⟨(-405825472515735049), (-405519672399302405)⟩, true⟩

def words02 : List Nat := [360582473403212079, 360582473661733718, 360582473662245653, 360582473631842501, 360582473601356872, 360582473158878958, 360582473284248712, 360582473568544236, 360582473569051120, 360582473764311941]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 41820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 41800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360588336544572959, 360588347367138401⟩, ⟨(-245934535401913719), (-245628510232015547)⟩, true⟩

def words03 : List Nat := [360582474374130799, 360582474984103760, 360582475681585729, 360582476212027783, 360582476258125148, 360582476304264719, 360582476304726788, 360582476563475054, 360582476704258954, 360582476845156804]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 41830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 41800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598410778255926, 360598421606245764⟩, ⟨(-667722084633267872), (-667415832481266060)⟩, true⟩

def words04 : List Nat := [360582476845668544, 360582476698439655, 360582475983071045, 360582475837835350, 360582475692451900, 360582475401418023, 360582475206242775, 360582474546429913, 360582473886539709, 360582474177690144]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 41840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 41800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk418
