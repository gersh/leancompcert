import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk866

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582173297778643, 360582222446944403⟩, ⟨(-5012140173161577), (-2137800711471343)⟩, true⟩

def state01 : KState := ⟨⟨360585381929444562, 360585431090468227⟩, ⟨(-282987152367555757), (-280111785951686543)⟩, true⟩

def words00 : List Nat := [360582197762418787, 360582197697248435, 360582197633087134, 360582197589888552, 360582197546336713, 360582197469368044, 360582197354089566, 360582197172270949, 360582196990217808, 360582196954088880]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 86600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 86600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577840122543503, 360577889295318391⟩, ⟨370238170224817937, 373114554472394899⟩, true⟩

def words01 : List Nat := [360582196988947868, 360582197024027515, 360582197025137414, 360582196993550124, 360582196983428400, 360582196895065999, 360582196806326066, 360582196829994406, 360582196831109704, 360582196782670878]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 86610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 86600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591070932519089, 360591120117044314⟩, ⟨(-775926140471207905), (-773048738351959497)⟩, true⟩

def words02 : List Nat := [360582196733952625, 360582196713556112, 360582196788693916, 360582196864067898, 360582196865257524, 360582196802053110, 360582196605377467, 360582196542207208, 360582196547263615, 360582196651560227]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 86620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 86600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576175135806064, 360576224332216797⟩, ⟨514608952000141605, 517487383819225171⟩, true⟩

def words03 : List Nat := [360582196674414798, 360582196697436290, 360582196799654717, 360582196969045581, 360582197104486853, 360582197240136889, 360582197308990323, 360582197310236502, 360582197245805112, 360582197178290427]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 86630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 86600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360561439655291696, 360561488863437985⟩, ⟨1791343974998873529, 1794223423645909457⟩, true⟩

def words04 : List Nat := [360582197110361355, 360582197105564309, 360582196967451059, 360582196761635131, 360582196555626885, 360582196253112588, 360582196053076110, 360582195873879914, 360582195694554931, 360582195423433899]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 86640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 86600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360578496748824652, 360578545968755785⟩, ⟨313217840792592297, 316098310652256893⟩, true⟩

def words05 : List Nat := [360582195185476511, 360582195047613881, 360582194909391756, 360582194767940563, 360582194551024843, 360582194223161861, 360582193895067585, 360582193678088037, 360582193578315807, 360582193537537833]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 86650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 86600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360565961304853285, 360566010536658375⟩, ⟨1399526345434045761, 1402407844348653421⟩, true⟩

def words06 : List Nat := [360582193496568807, 360582193389148345, 360582193148360861, 360582193009152362, 360582192869614472, 360582192696767039, 360582192479758813, 360582192160727509, 360582191841471082, 360582191543285220]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 86660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 86600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561338881793085, 360561388125336269⟩, ⟨1800179764284018883, 1803062280597632931⟩, true⟩

def words07 : List Nat := [360582191357603532, 360582191171519889, 360582190985304604, 360582190724762440, 360582190511391719, 360582190263746542, 360582190015739806, 360582189900938880, 360582189728584427, 360582189489902463]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 86670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 86600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360567696236831536, 360567745492156802⟩, ⟨1249033860399521215, 1251917398042886511⟩, true⟩

def words08 : List Nat := [360582189250953327, 360582188955979876, 360582188727724767, 360582188544832656, 360582188361841942, 360582188065654895, 360582187669858232, 360582187337385029, 360582187004515676, 360582186804857724]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 86680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 86600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360560418732811747, 360560468000009507⟩, ⟨1879944456216955749, 1882829023144130403⟩, true⟩

def words09 : List Nat := [360582186639393258, 360582186353761143, 360582186067896601, 360582185915314496, 360582185829453091, 360582185653332401, 360582185477099003, 360582185208763826, 360582184846793244, 360582184597738967]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 86690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 86600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 86600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk866
