import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk617A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk617B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk617A

def state06 : KState := ⟨⟨360626753680358311, 360626778019675990⟩, ⟨(-2729362181107230302), (-2728346703731491346)⟩, true⟩

def words05 : List Nat := [360582599070261679, 360582599115348065, 360582599313522092, 360582599652458554, 360582599745842971, 360582599839290912, 360582600194691801, 360582600704591084, 360582601420597417, 360582602136776888]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 61750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 61700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592210375215408, 360592234722790440⟩, ⟨(-595965016198863295), (-594949028808229189)⟩, true⟩

def words06 : List Nat := [360582602616600066, 360582602835362378, 360582603130844068, 360582603426566975, 360582603553712686, 360582603554578958, 360582603495901297, 360582603306301173, 360582603116527679, 360582603196203398]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 61760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 61700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579823291944859, 360579847647677284⟩, ⟨169263450642601131, 170279941955666909⟩, true⟩

def words07 : List Nat := [360582603558557461, 360582603921065822, 360582604120046725, 360582604137804703, 360582604138543113, 360582603969489736, 360582603833529804, 360582603921473883, 360582603922245550, 360582603878527975]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 61770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 61700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584390766695342, 360584415130615272⟩, ⟨(-112800330103607141), (-111783332926096945)⟩, true⟩

def words08 : List Nat := [360582604051890680, 360582604474750160, 360582605052708155, 360582605630813011, 360582605983815844, 360582606075946085, 360582606111507332, 360582606147318701, 360582606148034993, 360582606075365704]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 61780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 61700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585889025957927, 360585913398124948⟩, ⟨(-205412137052152816), (-204394630245713924)⟩, true⟩

def words09 : List Nat := [360582606076137795, 360582605954369691, 360582605892399027, 360582606087117315, 360582606126233468, 360582606165503001, 360582606166274896, 360582606073937213, 360582606040658989, 360582606095164710]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 61790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 61700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 61700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk617B
