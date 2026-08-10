import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk387A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk387B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk387A

def state06 : KState := ⟨⟨360610946916861687, 360610956147112295⟩, ⟨(-1111898090376014694), (-1111656269361262130)⟩, true⟩

def words05 : List Nat := [360582262988965798, 360582265055571999, 360582266889275437, 360582269058227815, 360582270851637897, 360582272645040281, 360582274105068657, 360582274903805682, 360582275644206899, 360582276384738743]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360623355686483826, 360623364921665463⟩, ⟨(-1593008522877158079), (-1592766510710886585)⟩, true⟩

def words06 : List Nat := [360582277635641752, 360582278225374973, 360582278395533328, 360582278565739179, 360582278568403950, 360582279130168683, 360582280355426884, 360582281580722201, 360582282473078019, 360582283533238266]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360603424850899325, 360603434091036048⟩, ⟨(-820202181898087003), (-819959977599238883)⟩, true⟩

def words07 : List Nat := [360582285112346641, 360582286691532866, 360582288031010868, 360582288709745934, 360582288729962168, 360582288750214717, 360582288991348077, 360582289656792157, 360582290202459527, 360582290748223866]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360612393704418893, 360612402949545699⟩, ⟨(-1168299607856434495), (-1168057210017198175)⟩, true⟩

def words08 : List Nat := [360582290913729811, 360582290914253983, 360582290586674057, 360582290754824776, 360582290755603087, 360582290985497268, 360582290985972244, 360582290701142118, 360582290620764816, 360582291397638886]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360608657690843404, 360608666940907128⟩, ⟨(-1023200129963025379), (-1022957540596147233)⟩, true⟩

def words09 : List Nat := [360582292837156938, 360582294276703609, 360582295311233478, 360582296675339677, 360582297872271833, 360582299069281266, 360582300363869461, 360582301375300075, 360582302055296828, 360582302735330052]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk387B
