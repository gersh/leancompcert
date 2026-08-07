import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk850

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360541990704148749, 360542037985761038⟩, ⟨3431258383544657006, 3433972482138100346⟩, true⟩

def state01 : KState := ⟨⟨360560765473143545, 360560812766300180⟩, ⟨1835282464227269868, 1837997544146786840⟩, true⟩

def words00 : List Nat := [360582437187741138, 360582436710201477, 360582436309518080, 360582436022390135, 360582435735184403, 360582435330405784, 360582434866121527, 360582434439216164, 360582434011927545, 360582433723177569]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 85000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 85000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360538932021353966, 360538979326134790⟩, ⟨3691508475147960815, 3694224543296903613⟩, true⟩

def words01 : List Nat := [360582433469934704, 360582433136564070, 360582432802966928, 360582432579063636, 360582432424431593, 360582432169918538, 360582431915281190, 360582431565509797, 360582431077205307, 360582430567528544]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 85010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 85000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360555678045394210, 360555725361689113⟩, ⟨2267676104552127774, 2270393151685761454⟩, true⟩

def words02 : List Nat := [360582430057451068, 360582429685861092, 360582429317938489, 360582428860785462, 360582428403447313, 360582427878072773, 360582427442593611, 360582427145563764, 360582426848425525, 360582426445444091]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 85020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 85000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579945323077828, 360579992650894826⟩, ⟨204049810347625026, 206767837262785254⟩, true⟩

def words03 : List Nat := [360582426132417053, 360582425884803393, 360582425636829684, 360582425383643061, 360582425151230704, 360582424801246247, 360582424451014573, 360582424239328536, 360582424096816219, 360582424069489168]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 85030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 85000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360571245583293358, 360571292922775016⟩, ⟨943768914617178583, 946487933548729967⟩, true⟩

def words04 : List Nat := [360582424042004081, 360582423908972105, 360582423676615039, 360582423441009683, 360582423205083109, 360582422915509121, 360582422586172345, 360582422187632261, 360582421788867358, 360582421528695636]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 85040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 85000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360544433689470212, 360544481040451187⟩, ⟨3224317503057560508, 3227037500065143064⟩, true⟩

def words05 : List Nat := [360582421398839714, 360582421316027035, 360582421233074690, 360582421080934865, 360582420900621627, 360582420685801881, 360582420470646488, 360582420208990626, 360582419852246131, 360582419407486987]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 85050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 85000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360557850044971851, 360557897407483081⟩, ⟨2083043404500725155, 2085764382327859987⟩, true⟩

def words06 : List Nat := [360582418962461088, 360582418655900344, 360582418418452013, 360582418120322059, 360582417822081877, 360582417405017451, 360582416849582672, 360582416406493725, 360582415963040011, 360582415620511504]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 85060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 85000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566451501998496, 360566498876164295⟩, ⟨1351233812990417991, 1353955782328467987⟩, true⟩

def words07 : List Nat := [360582415333410464, 360582414940561761, 360582414547482244, 360582414268318371, 360582414094026073, 360582413849647345, 360582413605153865, 360582413269527078, 360582412975574239, 360582412789919919]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 85070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 85000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571975247174366, 360572022632847389⟩, ⟨881232328966943954, 883955277395607102⟩, true⟩

def words08 : List Nat := [360582412603863629, 360582412556070044, 360582412448844933, 360582412263573928, 360582412078140583, 360582411743145359, 360582411498960270, 360582411393024709, 360582411286958328, 360582411107138089]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 85080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 85000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590885647470969, 360590933044702152⟩, ⟨(-727923434451779989), (-725199502483796035)⟩, true⟩

def words09 : List Nat := [360582411001958079, 360582411019246848, 360582411174151608, 360582411223872333, 360582411225011571, 360582411155948880, 360582411103884719, 360582411209003581, 360582411310148236, 360582411411554671]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 85090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 85000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 85000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk850
