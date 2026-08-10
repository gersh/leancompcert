import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk541A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk541B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk541A

def state06 : KState := ⟨⟨360546916454867083, 360546934976766481⟩, ⟨1890493814791575677, 1891171597369360047⟩, true⟩

def words05 : List Nat := [360581855758218778, 360581855961592098, 360581855962272704, 360581855899449973, 360581855496031723, 360581855006853782, 360581854517473965, 360581854235043894, 360581853855534811, 360581853211577585]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360609677884952551, 360609696413950259⟩, ⟨(-1508955015939742403), (-1508276848883661719)⟩, true⟩

def words06 : List Nat := [360581852567474120, 360581852126275020, 360581852106372155, 360581852266946692, 360581852267641174, 360581852102133894, 360581852312871748, 360581852588809788, 360581853015555258, 360581853530324636]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360574506409602466, 360574524945780623⟩, ⟨396446833885222294, 397125389940270156⟩, true⟩

def words07 : List Nat := [360581853832214940, 360581854134167443, 360581854353086067, 360581854743595470, 360581854908792951, 360581855074102065, 360581855074772246, 360581855069817048, 360581854821603474, 360581854687197018]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360568827980262378, 360568846523522083⟩, ⟨704136362881466007, 704815302650655323⟩, true⟩

def words08 : List Nat := [360581854757165460, 360581854757917802, 360581854623141217, 360581854318271887, 360581854013287589, 360581853622805002, 360581853494549580, 360581853358570251, 360581853222517511, 360581852895595356]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603672102259964, 360603690652620482⟩, ⟨(-1184224127890208753), (-1183544803292564741)⟩, true⟩

def words09 : List Nat := [360581852656194106, 360581852647851312, 360581852969856167, 360581853345767602, 360581853431341577, 360581853516973121, 360581853517588588, 360581853628348021, 360581854031853688, 360581854435515769]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk541B
