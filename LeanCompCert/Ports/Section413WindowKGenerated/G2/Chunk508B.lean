import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk508A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk508B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk508A

def state06 : KState := ⟨⟨360550624344653235, 360550640594853220⟩, ⟨1594389394214000629, 1594947847701914123⟩, true⟩

def words05 : List Nat := [360582002532003072, 360582002833562004, 360582002834193324, 360582002791679700, 360582002500083786, 360582001939556876, 360582001378842362, 360582001203986706, 360582000783034212, 360582000167163522]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 50800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577468306241656, 360577484563089383⟩, ⟨229086385753154200, 229645177377814852⟩, true⟩

def words06 : List Nat := [360581999551157913, 360581999253155371, 360581999420902997, 360581999588962198, 360581999589610442, 360581999426186584, 360581999081539005, 360581999102492673, 360581999103073974, 360581998916880966]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 50860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 50800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567212868237779, 360567229131774779⟩, ⟨750855935076308665, 751415067017848275⟩, true⟩

def words07 : List Nat := [360581998828766614, 360581998516210304, 360581998275777775, 360581998579799111, 360581998580392579, 360581998578766231, 360581998577055794, 360581998380722221, 360581997799127035, 360581997509664281]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 50870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 50800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583102512151967, 360583118782323290⟩, ⟨(-57790741464129888), (-57231271935207664)⟩, true⟩

def words08 : List Nat := [360581997219981425, 360581996883616581, 360581996627108100, 360581996074450859, 360581995521700662, 360581994872753138, 360581994525045715, 360581994472733936, 360581994420347458, 360581994196995134]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 50880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 50800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598551185685574, 360598567462493170⟩, ⟨(-844010488528750707), (-843450681247073637)⟩, true⟩

def words09 : List Nat := [360581994604854542, 360581995012904106, 360581995805909583, 360581996214046960, 360581996291518927, 360581996369032476, 360581996369614973, 360581996395333806, 360581996721464651, 360581997047742044]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 50890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 50800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 50800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk508B
