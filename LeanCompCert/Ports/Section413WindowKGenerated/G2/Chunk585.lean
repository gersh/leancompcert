import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk585

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk585
