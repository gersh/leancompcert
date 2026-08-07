import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk996

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589605272052234, 360589670993624273⟩, ⟨(-724682059910009876), (-720262132118013530)⟩, true⟩

def state01 : KState := ⟨⟨360590569111941188, 360590634847170451⟩, ⟨(-820745307650043937), (-816324019531223057)⟩, true⟩

def words00 : List Nat := [360582439669833462, 360582439720696553, 360582439722027336, 360582439684897524, 360582439647539489, 360582439545389528, 360582439568854661, 360582439631814926, 360582439644163724, 360582439727961416]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360583077339386243, 360583143088284744⟩, ⟨(-74428431404673803), (-70005781625621223)⟩, true⟩

def words01 : List Nat := [360582439912125680, 360582440096726899, 360582440287779104, 360582440378590817, 360582440379927708, 360582440379725892, 360582440379259867, 360582440350366873, 360582440358597601, 360582440367155408]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576096700583593, 360576162463280114⟩, ⟨620934729087686024, 625358753492715964⟩, true⟩

def words02 : List Nat := [360582440368457862, 360582440326418780, 360582440183605352, 360582440141951909, 360582440099888591, 360582440030713318, 360582439880843623, 360582439654973239, 360582439428829714, 360582439275018474]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360563358934791019, 360563424711151913⟩, ⟨1890030963348653185, 1894456349202532955⟩, true⟩

def words03 : List Nat := [360582439213209711, 360582439123847642, 360582439034322139, 360582438894525481, 360582438693660757, 360582438467717482, 360582438241350505, 360582438049812875, 360582437910799282, 360582437721481124]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577782528717963, 360577848318747989⟩, ⟨452822754924764925, 457249502839079909⟩, true⟩

def words04 : List Nat := [360582437531837573, 360582437401319623, 360582437339540509, 360582437359845697, 360582437361211862, 360582437291113617, 360582437120293617, 360582437033104187, 360582436945483714, 360582436873718778]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360570859058956032, 360570924862807714⟩, ⟨1142810332159316190, 1147238457469717456⟩, true⟩

def words05 : List Nat := [360582436828963623, 360582436721868988, 360582436614473294, 360582436634123596, 360582436635338856, 360582436634464129, 360582436633444459, 360582436581995126, 360582436500407603, 360582436386563180]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576297110163087, 360576362927643287⟩, ⟨600804640656146629, 605234124254183203⟩, true⟩

def words06 : List Nat := [360582436272227741, 360582436258797383, 360582436144792859, 360582435975329755, 360582435805634407, 360582435595244942, 360582435460323658, 360582435426300900, 360582435392120505, 360582435307740149]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581868722037656, 360581934553220556⟩, ⟨45339688735212580, 49770538148007526⟩, true⟩

def words07 : List Nat := [360582435248004857, 360582435111548377, 360582434974690399, 360582434807169082, 360582434639962069, 360582434386924115, 360582434133613276, 360582433964285863, 360582433859854092, 360582433856372122]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583696476178385, 360583762321165681⟩, ⟨(-136919670400862311), (-132487444899216997)⟩, true⟩

def words08 : List Nat := [360582433852654480, 360582433787435872, 360582433781933665, 360582433819273475, 360582433830741746, 360582433832191566, 360582433743382392, 360582433571033261, 360582433398405603, 360582433340165398]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360570134362252493, 360570200220888005⟩, ⟨1215207549536387012, 1219641135696652678⟩, true⟩

def words09 : List Nat := [360582433435596832, 360582433531304417, 360582433544699269, 360582433560502667, 360582433561716007, 360582433538309923, 360582433519443031, 360582433520893243, 360582433452774487, 360582433331577039]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk996
