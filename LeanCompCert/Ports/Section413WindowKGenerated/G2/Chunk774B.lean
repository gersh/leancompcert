import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk774A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk774B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk774A

def state06 : KState := ⟨⟨360558991886755460, 360559030869039123⟩, ⟨1790721101127225716, 1792760526997919348⟩, true⟩

def words05 : List Nat := [360582177061319868, 360582176804093246, 360582176546658625, 360582176414361963, 360582176391176283, 360582176253120199, 360582176114946930, 360582175893651804, 360582175505934905, 360582175208401348]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 77450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 77400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360563327074832069, 360563366067546722⟩, ⟨1454948329232951452, 1456988563139077208⟩, true⟩

def words06 : List Nat := [360582174910508479, 360582174733362440, 360582174643153717, 360582174445846099, 360582174248361840, 360582174009532050, 360582173853790597, 360582173684413344, 360582173514940954, 360582173200154688]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 77460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 77400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588831187405507, 360588870190554114⟩, ⟨(-521043927186101956), (-519002884909140022)⟩, true⟩

def words07 : List Nat := [360582172958285259, 360582172883065566, 360582172807518062, 360582172758604071, 360582172543442691, 360582172187505329, 360582171831346234, 360582171641803689, 360582171649330234, 360582171736934399]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 77470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 77400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592476177669751, 360592515191378368⟩, ⟨(-803622477171011479), (-801580616655869963)⟩, true⟩

def words08 : List Nat := [360582171740200514, 360582171741308734, 360582171672597481, 360582171600299260, 360582171527701727, 360582171413695294, 360582171317400094, 360582171116500620, 360582170915393623, 360582171014420323]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 77480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 77400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360555337090900745, 360555376115015147⟩, ⟨2074559837364909823, 2076602504278206253⟩, true⟩

def words09 : List Nat := [360582171315032390, 360582171615848456, 360582171809610940, 360582171837391442, 360582171838323492, 360582171755024124, 360582171671418028, 360582171584123317, 360582171330635563, 360582170986038092]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 77490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 77400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 77400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk774B
