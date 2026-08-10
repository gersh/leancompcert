import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk353A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk353B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk353A

def state06 : KState := ⟨⟨360616031753057009, 360616039377471106⟩, ⟨(-1204585901030675280), (-1204403637332488952)⟩, true⟩

def words05 : List Nat := [360581974178578513, 360581974338848697, 360581975297980855, 360581976139955228, 360581976301579938, 360581976463232680, 360581976602973644, 360581977224457336, 360581978188137985, 360581979151874192]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 35350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 35300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588002275060386, 360588009903992245⟩, ⟨(-213564019054204886), (-213381595585440664)⟩, true⟩

def words06 : List Nat := [360581979716806511, 360581979717280974, 360581980051885052, 360581980618778154, 360581980661890153, 360581980662364672, 360581979908939868, 360581978751714390, 360581977594463624, 360581977233285015]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 35360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 35300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360545645027599554, 360545652661008452⟩, ⟨1284751776760927685, 1284934358604335065⟩, true⟩

def words07 : List Nat := [360581977233675739, 360581977164565714, 360581977095409522, 360581976517101465, 360581975582032668, 360581974439146465, 360581973296183516, 360581972414788392, 360581971786512527, 360581970760460243]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 35370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 35300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597988213384066, 360597995851270592⟩, ⟨(-567330400433519725), (-567147660148815715)⟩, true⟩

def words08 : List Nat := [360581969734358191, 360581969675789062, 360581970308272502, 360581970940810857, 360581970941256007, 360581970804539617, 360581970444689523, 360581970200311114, 360581970203416994, 360581970656725403]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 35380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 35300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586840905569420, 360586848547985034⟩, ⟨(-172660984033961793), (-172478083442734033)⟩, true⟩

def words09 : List Nat := [360581970657148590, 360581970638491779, 360581971397751921, 360581972756827126, 360581973915628268, 360581975074441428, 360581975669746930, 360581976147167842, 360581976285198865, 360581976423371528]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 35390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 35300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 35300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk353B
