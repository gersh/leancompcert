import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk821

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360608215667574959, 360608259659276702⟩, ⟨(-2132003119651673260), (-2129563922400639312)⟩, true⟩

def state01 : KState := ⟨⟨360590228751708901, 360590272754635370⟩, ⟨(-655334480201181442), (-652894361347102520)⟩, true⟩

def words00 : List Nat := [360582321558656222, 360582321653437630, 360582321705148607, 360582321757195431, 360582321771729176, 360582321772906019, 360582321683497887, 360582321519955810, 360582321356187074, 360582321391707783]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360560356773754230, 360560400787750097⟩, ⟨1797658311116354857, 1800099338935675611⟩, true⟩

def words01 : List Nat := [360582321608345329, 360582321825203062, 360582321954688077, 360582321955864894, 360582321937319519, 360582321822748255, 360582321707838723, 360582321589172102, 360582321405863874, 360582321140148243]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586839532479743, 360586883557583872⟩, ⟨(-377274244399529878), (-374832304315500988)⟩, true⟩

def words02 : List Nat := [360582320874176788, 360582320652823274, 360582320505473981, 360582320445764388, 360582320385955625, 360582320200737320, 360582319992571995, 360582319834918381, 360582319676921634, 360582319722925637]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590124443782737, 360590168480114762⟩, ⟨(-647128953085972228), (-644686090800815756)⟩, true⟩

def words03 : List Nat := [360582319723992667, 360582319666892185, 360582319620798271, 360582319726516061, 360582319794747583, 360582319863169482, 360582319864227772, 360582319809431431, 360582319853365686, 360582319950259991]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585112902314196, 360585156949727258⟩, ⟨(-235456756714434258), (-233012984177006602)⟩, true⟩

def words04 : List Nat := [360582320194878599, 360582320337462550, 360582320405377264, 360582320473412072, 360582320474414534, 360582320480529871, 360582320517674225, 360582320555046473, 360582320556095597, 360582320551093316]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360589717451344167, 360589761509889922⟩, ⟨(-613693129978400765), (-611248442835592827)⟩, true⟩

def words05 : List Nat := [360582320707532946, 360582320864349371, 360582321168865273, 360582321325797792, 360582321356310461, 360582321386918482, 360582321498365842, 360582321684385728, 360582321775913865, 360582321867689419]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 82150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 82100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592648358032945, 360592692427797503⟩, ⟨(-854642025527249752), (-852196416593616372)⟩, true⟩

def words06 : List Nat := [360582321868752333, 360582321855860378, 360582321694968626, 360582321682477338, 360582321669673613, 360582321619937645, 360582321573420713, 360582321439439873, 360582321305236783, 360582321415924779]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 82160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 82100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360574291132360477, 360574335213227327⟩, ⟨653910821192927947, 656357342457332985⟩, true⟩

def words07 : List Nat := [360582321691108952, 360582321966512028, 360582322118345466, 360582322155934705, 360582322156923615, 360582322121484000, 360582322134358920, 360582322135539818, 360582322134953377, 360582322039005587]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 82170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 82100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594244897436349, 360594288989413461⟩, ⟨(-986013503702884226), (-983566069341004712)⟩, true⟩

def words08 : List Nat := [360582321942779129, 360582321828536076, 360582321894729643, 360582322002516594, 360582322003602942, 360582321985196057, 360582321978668699, 360582321939811964, 360582322008399247, 360582322155218221]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 82180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 82100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360591795744618791, 360591839847813906⟩, ⟨(-784672604560250259), (-782224248135711681)⟩, true⟩

def words09 : List Nat := [360582322227668882, 360582322300254177, 360582322520559078, 360582322862132240, 360582323115104307, 360582323368259729, 360582323546886860, 360582323619667708, 360582323736393782, 360582323853505617]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 82190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 82100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 82100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk821
