import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk912A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581612034914569, 360581666763122870⟩, ⟨25619636312873859, 28990072105407901⟩, true⟩

def state01 : KState := ⟨⟨360574304151551738, 360574358892189916⟩, ⟨692063438394306660, 695435007853237210⟩, true⟩

def words00 : List Nat := [360581984649243421, 360581984650562085, 360581984595617975, 360581984436817212, 360581984277809489, 360581984014172288, 360581983813326312, 360581983709000443, 360581983604526780, 360581983440022975]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 91200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 91200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584121512858320, 360584176265923474⟩, ⟨(-203417966919086753), (-200045263933136419)⟩, true⟩

def words01 : List Nat := [360581983376868765, 360581983397703547, 360581983502291616, 360581983527443539, 360581983528670424, 360581983450896076, 360581983372889523, 360581983270503772, 360581983266708366, 360581983292113353]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 91210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 91200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360572340020850159, 360572394786466455⟩, ⟨871245122714851486, 874618970678599680⟩, true⟩

def words02 : List Nat := [360581983293293163, 360581983242092954, 360581983150789828, 360581983078360233, 360581983005545318, 360581982867929211, 360581982610192709, 360581982284527992, 360581981958617724, 360581981753151522]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 91220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 91200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574155810417278, 360574210588466687⟩, ⟨705570916114110379, 708945898410900797⟩, true⟩

def words03 : List Nat := [360581981649151065, 360581981542735207, 360581981436190932, 360581981263594839, 360581981153161911, 360581980994030701, 360581980834515718, 360581980795263200, 360581980793903929, 360581980710106439]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 91230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 91200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597623409982717, 360597678200472167⟩, ⟨(-1435729002967673467), (-1432352885581127953)⟩, true⟩

def words04 : List Nat := [360581980626013164, 360581980651616637, 360581980825230099, 360581980999092517, 360581981050480759, 360581981051799817, 360581981037650168, 360581981049633493, 360581981181181101, 360581981354568220]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 91240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 91200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk912A
