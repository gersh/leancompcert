import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk956

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360604463811260126, 360604524168539703⟩, ⟨(-2138510310483817627), (-2134614015916433979)⟩, true⟩

def state01 : KState := ⟨⟨360612611534181925, 360612671904657169⟩, ⟨(-2917558225456352810), (-2913660669316943194)⟩, true⟩

def words00 : List Nat := [360582195956491107, 360582196077142666, 360582196306967070, 360582196537195107, 360582196739112952, 360582196943885737, 360582197093240983, 360582197242739249, 360582197468714392, 360582197789029083]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 95600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 95600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586870432777965, 360586930816323165⟩, ⟨(-456301858128907247), (-452403052304940379)⟩, true⟩

def words01 : List Nat := [360582198160605552, 360582198532448838, 360582198807057603, 360582198972724684, 360582199078080879, 360582199183811596, 360582199398530326, 360582199504450274, 360582199555165331, 360582199606104647]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 95610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 95600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597486427305394, 360597546823927408⟩, ⟨(-1471446098309497316), (-1467546042015841252)⟩, true⟩

def words02 : List Nat := [360582199766106588, 360582199980970429, 360582200211911018, 360582200443105025, 360582200568851684, 360582200611340071, 360582200617036855, 360582200623126093, 360582200738187800, 360582200900095013]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 95620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 95600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360598228486888710, 360598288896707657⟩, ⟨(-1542392455397884385), (-1538491137020229821)⟩, true⟩

def words03 : List Nat := [360582200999699410, 360582201099453729, 360582201308321526, 360582201620882751, 360582201887815592, 360582202154968338, 360582202358388152, 360582202452940136, 360582202622258746, 360582202792034764]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 95630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 95600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593323396452862, 360593383819347516⟩, ⟨(-1073282609899285067), (-1069380040895920787)⟩, true⟩

def words04 : List Nat := [360582202917064026, 360582203062367556, 360582203153064792, 360582203243899990, 360582203245069074, 360582203302431568, 360582203447023089, 360582203591902353, 360582203681570543, 360582203799892457]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 95640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 95600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360611197643324901, 360611258079305486⟩, ⟨(-2783033117382803972), (-2779129296644466048)⟩, true⟩

def words05 : List Nat := [360582204027236055, 360582204254996690, 360582204546999258, 360582204811252550, 360582204970675760, 360582205130190736, 360582205341154003, 360582205616479163, 360582205921308553, 360582206226443354]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 95650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 95600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360600432263936792, 360600492713152005⟩, ⟨(-1753179200487353449), (-1749274113659832981)⟩, true⟩

def words06 : List Nat := [360582206475829534, 360582206727967176, 360582207070029828, 360582207412492820, 360582207694599609, 360582207911775363, 360582208032495674, 360582208153350666, 360582208253379219, 360582208446094487]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 95660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 95600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587007323444332, 360587067785723415⟩, ⟨(-468739498024688263), (-464833161312049349)⟩, true⟩

def words07 : List Nat := [360582208696834859, 360582208947834997, 360582209143695447, 360582209230763558, 360582209263350562, 360582209296334046, 360582209419547733, 360582209526137760, 360582209578161089, 360582209630381059]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 95670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 95600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360599434344328262, 360599494819711377⟩, ⟨(-1657815636384303562), (-1653908045811872336)⟩, true⟩

def words08 : List Nat := [360582209767955365, 360582209977730774, 360582210184333655, 360582210391181648, 360582210505801722, 360582210511611253, 360582210600907354, 360582210690624909, 360582210796452552, 360582210978537057]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 95680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 95600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588864780211495, 360588925268802669⟩, ⟨(-646379112344925671), (-642470257832092843)⟩, true⟩

def words09 : List Nat := [360582211099148734, 360582211219909864, 360582211320468146, 360582211490109063, 360582211631513831, 360582211773142165, 360582211831582904, 360582211832970614, 360582211889381058, 360582211961127388]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 95690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 95600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 95600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk956
