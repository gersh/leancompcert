import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk815A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk815B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk815A

def state06 : KState := ⟨⟨362499103727777739, 362499203623875585⟩, ⟨(-1147052300284601453), (-1141550735630535423)⟩, true⟩

def words05 : List Nat := [371285206507862548, 371285206553324319, 371285206747612845, 371285206809722071, 371285206846523436, 371285206884177657, 371285206969355450, 371285206993795664, 371285207167322209, 371285207342127807]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362496483546572319, 362496583468150833⟩, ⟨(-933369485051967472), (-927865842062601790)⟩, true⟩

def words06 : List Nat := [371285207517960632, 371285207550677556, 371285207732782869, 371285207916375719, 371285208104200625, 371285208139134270, 371285208168404511, 371285208198640585, 371285208377984524, 371285208520656472]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482760739735649, 362482860686744138⟩, ⟨186081999781586240, 191587717223863202⟩, true⟩

def words07 : List Nat := [371285208706082687, 371285208892594099, 371285209078130973, 371285209080955320, 371285209076439781, 371285209090251554, 371285209194255470, 371285209197129116, 371285209176680494, 371285209151039601]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488111789464434, 362488211761741689⟩, ⟨(-250465046315472860), (-244957267317689066)⟩, true⟩

def words08 : List Nat := [371285209202383523, 371285209208658900, 371285209308304335, 371285209409128938, 371285209461978232, 371285209464809145, 371285209373301925, 371285209359948280, 371285209463592116, 371285209503314685]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490059197797802, 362490159195883422⟩, ⟨(-409335734986976396), (-403825850161482602)⟩, true⟩

def words09 : List Nat := [371285209542185566, 371285209582092220, 371285209755819426, 371285209855798186, 371285210000755688, 371285210146766394, 371285210281978796, 371285210284823082, 371285210346123080, 371285210410327345]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk815B
