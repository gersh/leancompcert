import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk594

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584536916878965, 360584559362224443⟩, ⟨(-150970974602319062), (-150070249553100398)⟩, true⟩

def state01 : KState := ⟨⟨360604388142102577, 360604410595270790⟩, ⟨(-1330224695769258147), (-1329323506010139199)⟩, true⟩

def words00 : List Nat := [360582033237354313, 360582033511718059, 360582033643288302, 360582033774944974, 360582033823497036, 360582034012977129, 360582034485688244, 360582034958543046, 360582035177709441, 360582035555193866]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 59400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 59400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360620822814087457, 360620845275089536⟩, ⟨(-2306820984153079419), (-2305919328944133347)⟩, true⟩

def words01 : List Nat := [360582035969386080, 360582036383803613, 360582036797628164, 360582037016684091, 360582037017451881, 360582036959319551, 360582037125440467, 360582037496097524, 360582038149878627, 360582038803826109]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 59410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 59400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360610169711189561, 360610192180112508⟩, ⟨(-1673895381809670756), (-1672993255905097294)⟩, true⟩

def words02 : List Nat := [360582039286652949, 360582039841567246, 360582040281095226, 360582040720837399, 360582041087954003, 360582041277780538, 360582041294161437, 360582041310624502, 360582041527021694, 360582042001655052]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 59420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 59400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360566978446695205, 360567000923440224⟩, ⟨893259248796490869, 894161839605886997⟩, true⟩

def words03 : List Nat := [360582042687784355, 360582043374055104, 360582043847486032, 360582044038943920, 360582044157720484, 360582044276726368, 360582044384231287, 360582044385062307, 360582044275254376, 360582044023029826]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 59430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 59400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360601585794262760, 360601608278848497⟩, ⟨(-1163903472202349754), (-1163000415301642238)⟩, true⟩

def words04 : List Nat := [360582043800733615, 360582043972235652, 360582044426654382, 360582044881237338, 360582045094967611, 360582045095798644, 360582045241679898, 360582045456763217, 360582045613304924, 360582045943222492]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 59440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 59400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360604234721584253, 360604257214092932⟩, ⟨(-1321446938799683393), (-1320543410841868595)⟩, true⟩

def words05 : List Nat := [360582046034830243, 360582046126511481, 360582046501122819, 360582047024289023, 360582047293914574, 360582047563660996, 360582047690893695, 360582047901672846, 360582048275861987, 360582048650314290]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 59450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 59400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360621948193744192, 360621970694078552⟩, ⟨(-2374813090181781606), (-2373909096869954454)⟩, true⟩

def words06 : List Nat := [360582049226267007, 360582049720644441, 360582050073535807, 360582050426499330, 360582050588172370, 360582051004194733, 360582051702893372, 360582052401727986, 360582052934734961, 360582053606811314]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 59460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 59400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360636953653440978, 360636976161634436⟩, ⟨(-3267191421417627927), (-3266286960686664179)⟩, true⟩

def words07 : List Nat := [360582054561596244, 360582055516617937, 360582056754250752, 360582057787843131, 360582058573722518, 360582059359635853, 360582060187148050, 360582061199167045, 360582062123102354, 360582063047182987]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 59470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 59400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360618502327886984, 360618524844006766⟩, ⟨(-2169740781463083460), (-2168835849235074456)⟩, true⟩

def words08 : List Nat := [360582063827111605, 360582064325508306, 360582064917431131, 360582065509576440, 360582066029055987, 360582066565556673, 360582066940033742, 360582067314598764, 360582067693121091, 360582068306896362]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 59480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 59400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588096441656392, 360588118965616557⟩, ⟨(-360689687528248540), (-359784288837878614)⟩, true⟩

def words09 : List Nat := [360582069084471352, 360582069862179531, 360582070424479759, 360582070771179388, 360582071001701242, 360582071232436497, 360582071745615364, 360582072067585291, 360582072169966712, 360582072272471268]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 59490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 59400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 59400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk594
