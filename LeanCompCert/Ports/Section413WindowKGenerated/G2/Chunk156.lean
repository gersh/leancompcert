import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk156

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360546635012079377, 360546636392991267⟩, ⟨524951570700399865, 524966156334841647⟩, true⟩

def state01 : KState := ⟨⟨360617478216373709, 360617479599132743⟩, ⟨(-580685826937368573), (-580671212478233939)⟩, true⟩

def words00 : List Nat := [360580287853931963, 360580287873455400, 360580287873632901, 360580284748939800, 360580281624615242, 360580277434181404, 360580278835448589, 360580281583503581, 360580281583679419, 360580283313662355]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 15600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 15600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360664578791566098, 360664580176174251⟩, ⟨(-1316314439632624650), (-1316299796299509358)⟩, true⟩

def words01 : List Nat := [360580288337151283, 360580293360053715, 360580299521728788, 360580303617845237, 360580304114864004, 360580304611832949, 360580304611994575, 360580304627037416, 360580310022557804, 360580315417432845]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 15610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 15600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360656891279866990, 360656892666341912⟩, ⟨(-1196890806461059526), (-1196876133959749022)⟩, true⟩

def words02 : List Nat := [360580318149930678, 360580318323435221, 360580319784260825, 360580321244961884, 360580321681484338, 360580321681681447, 360580321067323624, 360580318382660128, 360580317097727042, 360580321996905552]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 15620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 15600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360469701729560121, 360469703117886033⟩, ⟨1729610850012922765, 1729625551454414317⟩, true⟩

def words03 : List Nat := [360580324009482659, 360580326021835817, 360580326022012418, 360580325911171843, 360580321738221081, 360580315448429033, 360580309159384697, 360580304545976121, 360580300058116549, 360580292986904858]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 15630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 15600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360667485484167229, 360667486874345637⟩, ⟨(-1364592923134063443), (-1364578192710219505)⟩, true⟩

def words04 : List Nat := [360580285916552421, 360580283149646182, 360580287451737856, 360580291753317028, 360580292062582437, 360580292062778968, 360580288645287227, 360580288974764371, 360580293379400272, 360580298950717101]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 15640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 15600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360520685870700567, 360520687262755423⟩, ⟨933715021265170384, 933729781064402370⟩, true⟩

def words05 : List Nat := [360580301669987908, 360580304388935273, 360580307618592664, 360580312919655660, 360580316196978496, 360580319473915018, 360580319869869968, 360580319870066641, 360580316215914752, 360580312408417263]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 15650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 15600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360571610791983612, 360571612185890645⟩, ⟨135914932530585549, 135929721344367933⟩, true⟩

def words06 : List Nat := [360580308863975614, 360580308864172406, 360580307070345622, 360580302530063439, 360580297990328415, 360580291145857326, 360580287908063698, 360580288323246623, 360580288323423609, 360580286705440382]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 15660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 15600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360702820057174846, 360702821452943159⟩, ⟨(-1921030355286997068), (-1921015537297833688)⟩, true⟩

def words07 : List Nat := [360580289664599488, 360580293176907267, 360580296536705933, 360580298651626573, 360580298651809775, 360580296947309644, 360580296139543974, 360580299892700442, 360580307706734856, 360580315519820410]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 15670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 15600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360715292383014284, 360715293780656200⟩, ⟨(-2117175341037777306), (-2117160493661093914)⟩, true⟩

def words08 : List Nat := [360580321271300681, 360580322985545580, 360580328759009576, 360580334531794713, 360580339240649875, 360580345464592442, 360580348585850228, 360580351706727027, 360580356846482873, 360580365446346017]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 15680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 15600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602636105405141, 360602637504903380⟩, ⟨(-348918598335817265), (-348903721823986907)⟩, true⟩

def words09 : List Nat := [360580372880991040, 360580380314724994, 360580385691589141, 360580392972842183, 360580398296154878, 360580403618843122, 360580409452996016, 360580412921949761, 360580414337703980, 360580415753306413]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 15690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 15600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 15600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk156
