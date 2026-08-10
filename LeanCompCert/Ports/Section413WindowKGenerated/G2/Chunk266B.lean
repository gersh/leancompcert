import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk266A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk266B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk266A

def state06 : KState := ⟨⟨360586801764542387, 360586805996103121⟩, ⟨(-112611612721908791), (-112535303357237469)⟩, true⟩

def words05 : List Nat := [360582587432126671, 360582588489798964, 360582589762203085, 360582589762553042, 360582589632127173, 360582588313587934, 360582586995074927, 360582585491918044, 360582584866582351, 360582585025270923]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360534987866249202, 360534992101147527⟩, ⟨1268520476200976261, 1268596874562516919⟩, true⟩

def words06 : List Nat := [360582585025582947, 360582584477050705, 360582582526357427, 360582579989707787, 360582577453153507, 360582574554865394, 360582570725364011, 360582566195260931, 360582561665430724, 360582558538138998]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360400561847826803, 360400566086024318⟩, ⟨4854568212244637107, 4854644698611630453⟩, true⟩

def words07 : List Nat := [360582556754970833, 360582555993951154, 360582555232951289, 360582553485683338, 360582550337721563, 360582546134048418, 360582541930586733, 360582537216935320, 360582531103038400, 360582524283123705]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360528000358766919, 360528004600270318⟩, ⟨1453922271019714714, 1453998845604327272⟩, true⟩

def words08 : List Nat := [360582517463640459, 360582512045671875, 360582507335379080, 360582504026308626, 360582500717455874, 360582496180104412, 360582491457126515, 360582488135086724, 360582484813194866, 360582481889352534]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360545143571269057, 360545147816114178⟩, ⟨996156006098787883, 996232669890496695⟩, true⟩

def words09 : List Nat := [360582479848634703, 360582476623287399, 360582473398114884, 360582471573084506, 360582470464557068, 360582468701568035, 360582466938674908, 360582464095097668, 360582461298237531, 360582459901128804]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk266B
