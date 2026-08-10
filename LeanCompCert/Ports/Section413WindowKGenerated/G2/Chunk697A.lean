import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk697A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360533986422490412, 360534017722692529⟩, ⟨3389080297405298902, 3390553913004628438⟩, true⟩

def state01 : KState := ⟨⟨360574282797430117, 360574314106940653⟩, ⟨580214093591617342, 581688358035064004⟩, true⟩

def words00 : List Nat := [360582661988465365, 360582661430934511, 360582660976803099, 360582660656432579, 360582660336003218, 360582659840302014, 360582659432066571, 360582659056519894, 360582658680693917, 360582658510297920]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 69700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 69700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360549379399109195, 360549410718037237⟩, ⟨2316344931642946381, 2317819852626332291⟩, true⟩

def words01 : List Nat := [360582658391479214, 360582658146861292, 360582657902076606, 360582657587074812, 360582657376192866, 360582657083448921, 360582656790607464, 360582656352573623, 360582655884674244, 360582655408981390]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 69710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 69700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360541027873040852, 360541059201253381⟩, ⟨2898655899272735438, 2900131467618086776⟩, true⟩

def words02 : List Nat := [360582654932954930, 360582654624528922, 360582654171459984, 360582653591311018, 360582653011018811, 360582652378591243, 360582651849455219, 360582651309456647, 360582650769372044, 360582650072723596]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 69720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 69700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360594560538937743, 360594591876470247⟩, ⟨(-834482801051923284), (-833006582778928030)⟩, true⟩

def words03 : List Nat := [360582649477074488, 360582649041839428, 360582648606311914, 360582648335015489, 360582648151133198, 360582647791747742, 360582647432182205, 360582647277967297, 360582647416267589, 360582647588565300]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 69730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 69700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567018042359682, 360567049389314750⟩, ⟨1086338856854071264, 1087815732300072576⟩, true⟩

def words04 : List Nat := [360582647589470081, 360582647584525380, 360582647374025129, 360582647313555671, 360582647252831531, 360582647026018870, 360582646672119099, 360582646189177828, 360582645706045357, 360582645313792171]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 69740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 69700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk697A
