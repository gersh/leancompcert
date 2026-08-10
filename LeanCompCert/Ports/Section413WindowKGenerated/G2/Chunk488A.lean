import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk488A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586166677948161, 360586181588063417⟩, ⟨(-201046503699116209), (-200554836861244353)⟩, true⟩

def state01 : KState := ⟨⟨360580718754715684, 360580733671230586⟩, ⟨64685786320704641, 65177765492559213⟩, true⟩

def words00 : List Nat := [360582071942612591, 360582071818571684, 360582071574257995, 360582071573179178, 360582071571909704, 360582071371951943, 360582070981628571, 360582070184117216, 360582069386509826, 360582069007544714]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 48800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 48800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360550609353377288, 360550624276230620⟩, ⟨1534370093020105358, 1534862381602837400⟩, true⟩

def words01 : List Nat := [360582068980741504, 360582068804824857, 360582068628842156, 360582068208240129, 360582067368232182, 360582066295148706, 360582065221904577, 360582064567156292, 360582064132590361, 360582063489290900]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 48810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 48800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585517880815926, 360585532810015657⟩, ⟨(-169920997728873018), (-169428399284852070)⟩, true⟩

def words02 : List Nat := [360582062845865501, 360582062642286184, 360582063082434355, 360582063522695125, 360582063589947683, 360582063590620163, 360582063238578874, 360582063211075508, 360582063183377142, 360582063120693611]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 48820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 48800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558392557614367, 360558407493223289⟩, ⟨1154817283417003017, 1155310194853498547⟩, true⟩

def words03 : List Nat := [360582063121292933, 360582062925851737, 360582062818971836, 360582063118171804, 360582063312501103, 360582063506932831, 360582063507532077, 360582063451696881, 360582062976691982, 360582062493117915]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 48830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 48800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360546585186869611, 360546600128809007⟩, ⟨1731417029443114790, 1731910250091879458⟩, true⟩

def words04 : List Nat := [360582062009339156, 360582061463400221, 360582060498398146, 360582059285478274, 360582058072498314, 360582056755216063, 360582055759284387, 360582055181317365, 360582054603301431, 360582053767500755]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 48840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 48800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk488A
