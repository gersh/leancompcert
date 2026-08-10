import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk654A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582500967917615, 360582528385975079⟩, ⟨24372980926089783, 25584262488986907⟩, true⟩

def state01 : KState := ⟨⟨360581279592733769, 360581307019478731⟩, ⟨104158213230647235, 105370062999229915⟩, true⟩

def words00 : List Nat := [360582919577425848, 360582919566795488, 360582919399142953, 360582919074270954, 360582918749258617, 360582918326471379, 360582918083036722, 360582918073123360, 360582918063093671, 360582917936203991]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 65400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 65400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360597685015125880, 360597712450571101⟩, ⟨(-969016261834455941), (-967803842939367833)⟩, true⟩

def words01 : List Nat := [360582918070305493, 360582918229311094, 360582918621303656, 360582918780416759, 360582918781281832, 360582918717259605, 360582918653062167, 360582918530009260, 360582918749786028, 360582918976870923]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 65410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 65400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585174599245347, 360585202043487290⟩, ⟨(-150530306359454705), (-149317311939271607)⟩, true⟩

def words02 : List Nat := [360582919087171897, 360582919203804487, 360582919553463305, 360582919903383031, 360582920191774530, 360582920247357108, 360582920248178471, 360582920181505377, 360582920114668241, 360582919985870270]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 65420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 65400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360549823040415308, 360549850493336281⟩, ⟨2162764302092511221, 2163977864424949909⟩, true⟩

def words03 : List Nat := [360582920180533628, 360582920375367445, 360582920406684454, 360582920407606477, 360582920205964766, 360582919876040069, 360582919545834808, 360582919448960664, 360582919119109439, 360582918614736418]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 65430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 65400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592621784408753, 360592649246049760⟩, ⟨(-638297872464175670), (-637083739451579470)⟩, true⟩

def words04 : List Nat := [360582918110170566, 360582917746749827, 360582917531880835, 360582917311562171, 360582917091178494, 360582916672511655, 360582916107735914, 360582915776330132, 360582915444653497, 360582915495007735]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 65440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 65400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk654A
