import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk594A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk594B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk594A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk594B
