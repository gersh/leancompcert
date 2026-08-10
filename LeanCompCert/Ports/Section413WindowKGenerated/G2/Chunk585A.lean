import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk585A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582046551053669, 360582068295008612⟩, ⟨(-5102166833887006), (-4242789603456372)⟩, true⟩

def state01 : KState := ⟨⟨360573502217951341, 360573523969593365⟩, ⟨494742225191632869, 495602052155264085⟩, true⟩

def words00 : List Nat := [360581995899103952, 360581995899920913, 360581995737714593, 360581995428598748, 360581995119360019, 360581994735574742, 360581994568082192, 360581994568662058, 360581994569165113, 360581994351616187]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598525198137398, 360598546957505431⟩, ⟨(-969535698105647859), (-968675419055620833)⟩, true⟩

def words01 : List Nat := [360581994354912963, 360581994503211494, 360581994530801306, 360581994531620608, 360581994461710182, 360581994140879018, 360581993819902338, 360581993778050491, 360581994061574817, 360581994345296897]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596916911557187, 360596938678697074⟩, ⟨(-875545354490151427), (-874684620591604147)⟩, true⟩

def words02 : List Nat := [360581994482023992, 360581994482841969, 360581994633460270, 360581994801186044, 360581994893108800, 360581994901363470, 360581994902111055, 360581994682590337, 360581994467606305, 360581994723859611]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360566657302103768, 360566679076941500⟩, ⟨895732184435439496, 896593368927471378⟩, true⟩

def words03 : List Nat := [360581994885654168, 360581995047593535, 360581995056730614, 360581995159142225, 360581995159827284, 360581995108740689, 360581995297306138, 360581995298123655, 360581995247689004, 360581994986899264]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604450672137093, 360604472454700540⟩, ⟨(-1316915794062564424), (-1316054157269553744)⟩, true⟩

def words04 : List Nat := [360581994725944723, 360581994456853891, 360581994652061666, 360581994896058777, 360581994896819702, 360581994892200294, 360581994691966403, 360581994706768905, 360581995013080037, 360581995397822442]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk585A
