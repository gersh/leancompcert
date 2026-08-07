import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk967

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360591999052888004, 360592060861787709⟩, ⟨(-945315507766509749), (-941279638396609821)⟩, true⟩

def state01 : KState := ⟨⟨360599267550671132, 360599329372806187⟩, ⟨(-1648228366866854791), (-1644191217573120237)⟩, true⟩

def words00 : List Nat := [360582327026340071, 360582327176715865, 360582327433617395, 360582327690782617, 360582327846313339, 360582327895333324, 360582327943397356, 360582327991866686, 360582328117937272, 360582328295187580]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 96700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 96700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580383005089123, 360580444840611666⟩, ⟨178223752565852210, 182262196627982450⟩, true⟩

def words01 : List Nat := [360582328418473416, 360582328541944176, 360582328701353855, 360582328913868835, 360582329053006538, 360582329192367602, 360582329271366640, 360582329288643861, 360582329289798642, 360582329271925024]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 96710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 96700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586332569256254, 360586394417989917⟩, ⟨(-397283850199025489), (-393244128292613015)⟩, true⟩

def words02 : List Nat := [360582329331726402, 360582329333129923, 360582329330441349, 360582329245670115, 360582329160673494, 360582329026931872, 360582329017674784, 360582329059653373, 360582329060906404, 360582329080835411]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 96720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 96700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360609451490866094, 360609513352863800⟩, ⟨(-2633744546916630124), (-2629703541912054352)⟩, true⟩

def words03 : List Nat := [360582329230877147, 360582329381342567, 360582329488077438, 360582329578638669, 360582329579933183, 360582329580081366, 360582329685577610, 360582329861255365, 360582330143385335, 360582330425853411]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 96730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 96700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604084279420094, 360604146154798635⟩, ⟨(-2114597513478464958), (-2110555213949488234)⟩, true⟩

def words04 : List Nat := [360582330654295776, 360582330776369512, 360582330979957439, 360582331183954822, 360582331319175994, 360582331442554608, 360582331469092155, 360582331495760353, 360582331629004288, 360582331856094235]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 96740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 96700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360596556259149513, 360596618147742090⟩, ⟨(-1386181412371294035), (-1382137834317724503)⟩, true⟩

def words05 : List Nat := [360582332147277867, 360582332438723722, 360582332676296045, 360582332916472931, 360582333106483948, 360582333296873232, 360582333593666908, 360582333811424114, 360582333960319123, 360582334109396913]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 96750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 96700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360600013725545224, 360600075627408108⟩, ⟨(-1720761484702630509), (-1716716622546083369)⟩, true⟩

def words06 : List Nat := [360582334222020022, 360582334388167162, 360582334660720468, 360582334933541110, 360582335115937714, 360582335191995446, 360582335242952842, 360582335294354597, 360582335452113926, 360582335636888779]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 96760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 96700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360600889510783329, 360600951426008379⟩, ⟨(-1805564921396197005), (-1801518766116384285)⟩, true⟩

def words07 : List Nat := [360582335767759354, 360582335898787213, 360582336042700216, 360582336244671246, 360582336369777405, 360582336495087639, 360582336566925829, 360582336653888252, 360582336847364449, 360582337041303568]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 96770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 96700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605892161512653, 360605954089985119⟩, ⟨(-2289735416682501082), (-2285687979251458902)⟩, true⟩

def words08 : List Nat := [360582337271002368, 360582337532625098, 360582337740379112, 360582337948284184, 360582338097938149, 360582338311395435, 360582338631195250, 360582338951257663, 360582339169848910, 360582339415281361]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 96780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 96700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360629995793652962, 360630057735384015⟩, ⟨(-4622896890189522664), (-4618848169395591044)⟩, true⟩

def words09 : List Nat := [360582339746299640, 360582340077724468, 360582340476912832, 360582340769974317, 360582340970570503, 360582341171282774, 360582341478448927, 360582341866199587, 360582342360267463, 360582342854655556]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 96790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 96700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 96700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk967
