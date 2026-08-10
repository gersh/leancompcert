import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk996A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk996B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk996A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk996B
