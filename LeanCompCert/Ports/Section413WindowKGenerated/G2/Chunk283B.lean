import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk283A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk283B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk283A

def state06 : KState := ⟨⟨360509915334231026, 360509920148324982⟩, ⟨2052909397771337197, 2053001738077842765⟩, true⟩

def words05 : List Nat := [360582319530652973, 360582320561847820, 360582320799293741, 360582320799667769, 360582319799367171, 360582318271165530, 360582316742966517, 360582315183922528, 360582313452993739, 360582310900725471]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360573921767838393, 360573926585463628⟩, ⟨237505500365420162, 237597940836609304⟩, true⟩

def words06 : List Nat := [360582308348552863, 360582306680942091, 360582305932569081, 360582306031615697, 360582306031961028, 360582305061906498, 360582303740231425, 360582302952398927, 360582302164510848, 360582301556941831]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360541482463850075, 360541487285045003⟩, ⟨1157963569467033069, 1158056111227737923⟩, true⟩

def words07 : List Nat := [360582301262086417, 360582300009049765, 360582298756030618, 360582297924050231, 360582297716449496, 360582297106842236, 360582296497240539, 360582295267778265, 360582294082290812, 360582292644848659]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360570765566698838, 360570770391415786⟩, ⟨326649577817330372, 326742219550857696⟩, true⟩

def words08 : List Nat := [360582291207381269, 360582290661808856, 360582289570215643, 360582287859632824, 360582286149114948, 360582283574562766, 360582281771067219, 360582281204123607, 360582280637179042, 360582279451632442]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360573583576336861, 360573588404594035⟩, ⟨246529187234098461, 246621929492253989⟩, true⟩

def words09 : List Nat := [360582279046560706, 360582278308110930, 360582278066756707, 360582278067131342, 360582277330865014, 360582275542441967, 360582273754073114, 360582272856196232, 360582272580743529, 360582272275350805]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk283B
