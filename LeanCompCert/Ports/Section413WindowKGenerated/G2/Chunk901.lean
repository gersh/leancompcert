import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk901

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360564291647250830, 360564345012850654⟩, ⟨1585747690300033487, 1588994604029098967⟩, true⟩

def state01 : KState := ⟨⟨360573110097625226, 360573163475489923⟩, ⟨791120030528899961, 794368049386053829⟩, true⟩

def words00 : List Nat := [360581980718329593, 360581980542783816, 360581980428705339, 360581980304299253, 360581980179772243, 360581979950711833, 360581979598418886, 360581979369590437, 360581979140371598, 360581979012604406]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360579439008932250, 360579492399200870⟩, ⟨220746527239995843, 223995663874612207⟩, true⟩

def words01 : List Nat := [360581978915953638, 360581978722977815, 360581978529748260, 360581978426617880, 360581978400511747, 360581978324115930, 360581978247591255, 360581978077621780, 360581977951971818, 360581977925875023]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575290423443311, 360575343825950097⟩, ⟨594617358321567643, 597867597922322113⟩, true⟩

def words02 : List Nat := [360581977994786714, 360581977996087180, 360581977969737805, 360581977850954206, 360581977731981403, 360581977522110506, 360581977373011244, 360581977347173192, 360581977321198841, 360581977217694493]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596755368232509, 360596808783032431⟩, ⟨(-1340085289674022408), (-1336833942033394436)⟩, true⟩

def words03 : List Nat := [360581977175801235, 360581977207913710, 360581977340733385, 360581977515907739, 360581977585246930, 360581977654677237, 360581977781945478, 360581977975503587, 360581978141104192, 360581978306977879]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360606686443675057, 360606739870857250⟩, ⟨(-2235420530413349732), (-2232168066573428226)⟩, true⟩

def words04 : List Nat := [360581978410869504, 360581978479357523, 360581978647626743, 360581978816287933, 360581978896501110, 360581979008192912, 360581979054346834, 360581979100642674, 360581979269631233, 360581979545774074]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360576459955879557, 360576513395334969⟩, ⟨489667596579506613, 492921166908769489⟩, true⟩

def words05 : List Nat := [360581979863048515, 360581980180562794, 360581980400996335, 360581980498658024, 360581980507350850, 360581980516390776, 360581980618528795, 360581980635861131, 360581980637020711, 360581980577754100]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 90150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 90100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584196774703374, 360584250226434471⟩, ⟨(-207888463722127876), (-204633786555710982)⟩, true⟩

def words06 : List Nat := [360581980524063359, 360581980593247426, 360581980784935021, 360581980976867844, 360581981064225507, 360581981065526658, 360581981029916268, 360581980930848306, 360581980831390049, 360581980829549046]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 90160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 90100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593859683713811, 360593913147844531⟩, ⟨(-1079249593897478900), (-1075993798597525468)⟩, true⟩

def words07 : List Nat := [360581980830719686, 360581980781924660, 360581980805664725, 360581980976381668, 360581981115190176, 360581981254206781, 360581981331331905, 360581981389577146, 360581981522940210, 360581981656747765]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 90170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 90100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581236957514053, 360581290433913830⟩, ⟨59053944067766673, 62310845853647603⟩, true⟩

def words08 : List Nat := [360581981738902245, 360581981740203856, 360581981735370092, 360581981652890008, 360581981570202318, 360581981415763663, 360581981351414673, 360581981381460680, 360581981382639016, 360581981318112230]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 90180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 90100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360606897928597604, 360606951417280685⟩, ⟨(-2255479292354204155), (-2252221282675307103)⟩, true⟩

def words09 : List Nat := [360581981426679456, 360581981543286880, 360581981666365028, 360581981754115373, 360581981755336744, 360581981726056716, 360581981788770340, 360581981944225043, 360581982222100571, 360581982500276713]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 90100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 90100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk901
