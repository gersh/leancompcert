import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk610

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360566222224590070, 360566245945322044⟩, ⟨988348153434809820, 989325661531329580⟩, true⟩

def state01 : KState := ⟨⟨360610417120069627, 360610440848863728⟩, ⟨(-1707700479366843921), (-1706722479441249443)⟩, true⟩

def words00 : List Nat := [360582464136466217, 360582464277378772, 360582464602607826, 360582464927990011, 360582465007918657, 360582465154643523, 360582465569861814, 360582465985318478, 360582466376918052, 360582466836317774]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 61000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 61000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568449068820104, 360568472805766505⟩, ⟨853048141795349515, 854026639132462635⟩, true⟩

def words01 : List Nat := [360582467161145853, 360582467486064576, 360582467771691495, 360582468191264618, 360582468541866640, 360582468892597593, 360582469020680994, 360582469021535652, 360582468882055037, 360582468653671003]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 61010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 61000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595444651314141, 360595468396309009⟩, ⟨(-794399173179106682), (-793420184684196742)⟩, true⟩

def words02 : List Nat := [360582468425000670, 360582468410966751, 360582468318750976, 360582468091625242, 360582467864368146, 360582467569863230, 360582467667790264, 360582467851513098, 360582467900834210, 360582468114735970]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 61020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 61000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360598575102917783, 360598598855988294⟩, ⟨(-985457806991813605), (-984478325599514921)⟩, true⟩

def words03 : List Nat := [360582468596901771, 360582469079302751, 360582469553799742, 360582469761049630, 360582469761841396, 360582469737384502, 360582469876127037, 360582470177224623, 360582470442152135, 360582470707275142]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 61030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 61000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591310292224215, 360591334053437184⟩, ⟨(-542084073791922170), (-541104095346299920)⟩, true⟩

def words04 : List Nat := [360582470837343797, 360582470842546238, 360582471115933655, 360582471389563132, 360582471538159632, 360582471539014781, 360582471487822508, 360582471192570717, 360582470897160881, 360582470904670640]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 61040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 61000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360588155540562758, 360588179309814695⟩, ⟨(-349373224460892127), (-348392755194722903)⟩, true⟩

def words05 : List Nat := [360582471318822813, 360582471733125426, 360582471992069197, 360582472288841878, 360582472516796453, 360582472744979321, 360582473241137175, 360582473470286062, 360582473564494125, 360582473658823151]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 61050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 61000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360604464526590003, 360604488303927063⟩, ⟨(-1345390590612777968), (-1344409627630195448)⟩, true⟩

def words06 : List Nat := [360582473659534725, 360582473537688544, 360582473751466400, 360582473965403579, 360582473966200726, 360582473916665452, 360582473782559384, 360582473815784169, 360582474063191120, 360582474424546831]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 61060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 61000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360596482133396685, 360596505918875017⟩, ⟨(-857845130601042863), (-856863670391204051)⟩, true⟩

def words07 : List Nat := [360582474651014918, 360582474877574967, 360582475316542050, 360582475942942869, 360582476376299832, 360582476809769065, 360582477108438298, 360582477140207755, 360582477370578022, 360582477601224828]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 61070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 61000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584669458823819, 360584693252369543⟩, ⟨(-136267986532392919), (-135286033525525007)⟩, true⟩

def words08 : List Nat := [360582477921771503, 360582478248939509, 360582478371240837, 360582478493619481, 360582478494336837, 360582478620952220, 360582478720333109, 360582478819872453, 360582478820647788, 360582478752139959]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 61080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 61000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360639081418957608, 360639105220579876⟩, ⟨(-3460603380186723918), (-3459620933743626478)⟩, true⟩

def words09 : List Nat := [360582479056975621, 360582479362061278, 360582479888676848, 360582480374054094, 360582480632820655, 360582480891660541, 360582481358517167, 360582482018392073, 360582482945813800, 360582483873404812]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 61090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 61000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 61000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk610
