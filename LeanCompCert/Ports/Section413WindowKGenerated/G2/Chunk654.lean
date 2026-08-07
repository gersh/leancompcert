import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk654

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

def state06 : KState := ⟨⟨360573527339159493, 360573554809572793⟩, ⟨611506221698741675, 612720928902234439⟩, true⟩

def words05 : List Nat := [360582915527653459, 360582915560398801, 360582915593478488, 360582915743638917, 360582915744416390, 360582915720159640, 360582915695825127, 360582915492706468, 360582915185686775, 360582915043744841]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561036341112785, 360561063820209710⟩, ⟨1429185679739187397, 1430400955417679919⟩, true⟩

def words06 : List Nat := [360582914901506260, 360582914784956148, 360582914505218893, 360582914108797778, 360582913712222062, 360582913257338349, 360582912919211599, 360582912660448253, 360582912401587923, 360582912009539444]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585941902686126, 360585969390501893⟩, ⟨(-201614530378128105), (-200398683833978383)⟩, true⟩

def words07 : List Nat := [360582911676590771, 360582911297712044, 360582910918566817, 360582910732018596, 360582910443475454, 360582909940136432, 360582909436636512, 360582909071772973, 360582908933165776, 360582908980858883]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563266115964768, 360563293612565465⟩, ⟨1283156575170266593, 1284372996993493411⟩, true⟩

def words08 : List Nat := [360582908981686178, 360582908854698825, 360582908601738043, 360582908385544178, 360582908169113719, 360582907792207645, 360582907242254503, 360582906563620754, 360582905884831381, 360582905354770283]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360555183048937681, 360555210554241470⟩, ⟨1812651034051165735, 1813868025883731125⟩, true⟩

def words09 : List Nat := [360582905056059587, 360582904931015018, 360582904805867011, 360582904536858579, 360582904353130886, 360582904111156047, 360582903868917914, 360582903859549022, 360582903617696256, 360582903195858016]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk654
