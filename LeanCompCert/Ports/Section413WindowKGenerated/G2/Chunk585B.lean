import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk585A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk585B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk585A

def state06 : KState := ⟨⟨360595450069038677, 360595471859385980⟩, ⟨(-789941320322459170), (-789079227745719732)⟩, true⟩

def words05 : List Nat := [360581995605626718, 360581995813516453, 360581996064515085, 360581996464206976, 360581996653397674, 360581996842703259, 360581996859048259, 360581996914098032, 360581997144864648, 360581997375894481]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360609736179192697, 360609757977252149⟩, ⟨(-1626572033367239139), (-1625709489129002555)⟩, true⟩

def words06 : List Nat := [360581997834697430, 360581998376721961, 360581998765923803, 360581999155199686, 360581999302268878, 360581999634797260, 360582000258650879, 360582000882639918, 360582001283744846, 360582001758489810]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360637891034760408, 360637912840541243⟩, ⟨(-3275802333099732466), (-3274939336581669896)⟩, true⟩

def words07 : List Nat := [360582002401219734, 360582003044175724, 360582003978385379, 360582004621971782, 360582004973472269, 360582005325032721, 360582005803700914, 360582006467523896, 360582007422544708, 360582008377719140]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360628512229309723, 360628534042899527⟩, ⟨(-2726498097935539022), (-2725634643931557810)⟩, true⟩

def words08 : List Nat := [360582009149329725, 360582009823376112, 360582010488952862, 360582011154735430, 360582011745724019, 360582012295169009, 360582012663064106, 360582013031035986, 360582013566706348, 360582014361652722]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360570230044981887, 360570251866272726⟩, ⟨688635210183269646, 689499115429808678⟩, true⟩

def words09 : List Nat := [360582015241907847, 360582016122286572, 360582016856073345, 360582017299378096, 360582017668070764, 360582018036969612, 360582018255770055, 360582018261987578, 360582018262725426, 360582018062781768]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk585B
