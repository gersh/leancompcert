import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk005

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨363010777886803560, 363010777887742612⟩, ⟨(-1306169030814383078), (-1306169030492241944)⟩, true⟩

def state01 : KState := ⟨⟨364205310302825326, 364205310303805806⟩, ⟨(-1930086709401584869), (-1930086709058520207)⟩, true⟩

def words00 : List Nat := [360406708907829662, 360406708907833985, 360409440624338882, 360412665922270306, 360414451468382655, 360416968789354393, 360417035782708551, 360417102512827985, 360420826560548868, 360428232595276413]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨359728929565720581, 359728929566742945⟩, ⟨372646407282248701, 372646407646888893⟩, true⟩

def words01 : List Nat := [360435035974373034, 360441812829575332, 360446278204785868, 360447319652379883, 360447319652383601, 360447055315544263, 360446792001283390, 360446938059310190, 360446938059314183, 360445557273756193]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362711737206902139, 362711737207967239⟩, ⟨(-1184626622425019376), (-1184626622037941370)⟩, true⟩

def words02 : List Nat := [360446269697508773, 360450583669559672, 360458326879539523, 360466040591577443, 360470299955188039, 360471285900194891, 360472487826676272, 360473685209013453, 360476592638079633, 360480801949892020]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨358478947699810954, 358478947700919911⟩, ⟨1087197359908846133, 1087197360319389301⟩, true⟩

def words03 : List Nat := [360482883486209392, 360484957211884476, 360487080214514066, 360491098394430382, 360494012065768856, 360496914885445752, 360498014911044593, 360498014911049236, 360496011449188088, 360492276145955818]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360363262518706865, 360363262519860055⟩, ⟨53756649356169093, 53756649790825049⟩, true⟩

def words04 : List Nat := [360488554651606488, 360488036943198638, 360484442205832757, 360479135807579867, 360473848882347356, 360467597409671595, 360464083695528284, 360463696367014216, 360463310449532500, 360461001883116101]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨359757142621800395, 359757142622998941⟩, ⟨382015387444275906, 382015387904108266⟩, true⟩

def words05 : List Nat := [360461001991810883, 360461178843989591, 360461178843993527, 360460927581291666, 360457691838393898, 360451428607216470, 360445187865198588, 360441970373172000, 360440533299029830, 360439312958541992]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨357747838504625012, 357747838505870455⟩, ⟨1499784978912155423, 1499784979398487289⟩, true⟩

def words06 : List Nat := [360438096968643450, 360434036494064707, 360427066728633442, 360423067329366357, 360419082087263617, 360414200916841393, 360406432375287476, 360396304180525001, 360386211585743231, 360379040224113416]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨358192689496821268, 358192689498113873⟩, ⟨1251352272896925057, 1251352273410385957⟩, true⟩

def words07 : List Nat := [360374432165066257, 360372716598709919, 360371007020368217, 360367702439517702, 360365248761496344, 360361248279228134, 360357261663448171, 360356108431974077, 360353919676710364, 360350193417786953]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨358498609326376416, 358498609327717137⟩, ⟨1068362681128941335, 1068362681670550703⟩, true⟩

def words08 : List Nat := [360346479985915614, 360342435606080923, 360340158977037482, 360337826095924977, 360335501190474046, 360330688607786485, 360323182128691121, 360318410615950281, 360313655305288575, 360309393533938410]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨359874108703691124, 359874108705081280⟩, ⟨245958426886451929, 245958427457479501⟩, true⟩

def words09 : List Nat := [360306329601275954, 360301851158231963, 360297387819548051, 360295932728135422, 360295932728139859, 360293749214609289, 360291573016031377, 360288023771569394, 360284723775955962, 360284039417510413]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk005
