import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk756A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580719347655039, 360580756409285992⟩, ⟨107417916625748391, 109310347174333687⟩, true⟩

def state01 : KState := ⟨⟨360557770199481804, 360557807271249615⟩, ⟨1842441246681268508, 1844334443627733994⟩, true⟩

def words00 : List Nat := [360582202295097593, 360582202269973810, 360582202116197238, 360582201812921621, 360582201509478127, 360582201162085151, 360582200902145256, 360582200635565570, 360582200368880303, 360582200002946848]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 75600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 75600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360609390990190178, 360609428072121168⟩, ⟨(-2060884734829454954), (-2058990769394390306)⟩, true⟩

def words01 : List Nat := [360582199681209508, 360582199534498389, 360582199387475287, 360582199451953416, 360582199452947107, 360582199377177606, 360582199399029527, 360582199585632945, 360582199946573781, 360582200307751557]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 75610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 75600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590785721114032, 360590822813316363⟩, ⟨(-654009135028217638), (-652114392824165028)⟩, true⟩

def words02 : List Nat := [360582200527452554, 360582200572610752, 360582200737608717, 360582200902919829, 360582200955463654, 360582200956540907, 360582200834520481, 360582200625885361, 360582200417030126, 360582200497165259]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 75620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 75600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360569398952725229, 360569436055074152⟩, ⟨963632494935264235, 965528004576055447⟩, true⟩

def words03 : List Nat := [360582200730703029, 360582200964441619, 360582201075383429, 360582201134442054, 360582201135359602, 360582201074697474, 360582201064702751, 360582201065780408, 360582201003316846, 360582200835674047]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 75630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 75600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360578069917626430, 360578107030161589⟩, ⟨307813086400476573, 309709366578129247⟩, true⟩

def words04 : List Nat := [360582200673610845, 360582200814496995, 360582201081092889, 360582201347887886, 360582201454182215, 360582201455259837, 360582201427671998, 360582201301503321, 360582201175037178, 360582201007247883]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 75640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 75600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk756A
