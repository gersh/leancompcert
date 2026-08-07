import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk777

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603027836619449, 360603067070448631⟩, ⟨(-1624305131085216751), (-1622246190305546341)⟩, true⟩

def state01 : KState := ⟨⟨360579694549432169, 360579733793704938⟩, ⟨188750247012665250, 190809999312368248⟩, true⟩

def words00 : List Nat := [360582189274423455, 360582189374019345, 360582189375008009, 360582189373300679, 360582189371405189, 360582189369686278, 360582189370601410, 360582189342969480, 360582189315217515, 360582189204840087]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 77700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 77700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360619045049280520, 360619084304022386⟩, ⟨(-2869363825820340679), (-2867303259915459285)⟩, true⟩

def words01 : List Nat := [360582189307902018, 360582189442882660, 360582189742887637, 360582190125855235, 360582190340681635, 360582190555571999, 360582190783034945, 360582191093623516, 360582191569214517, 360582192045045849]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 77710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 77700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360612365697008682, 360612404962334849⟩, ⟨(-2350323957917072771), (-2348262569347123289)⟩, true⟩

def words02 : List Nat := [360582192393214566, 360582192576327610, 360582192924549531, 360582193273102830, 360582193578169206, 360582193858839932, 360582194033371393, 360582194208033817, 360582194455867196, 360582194845787434]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 77720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 77700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579504702170680, 360579543977939796⟩, ⟨204207094223951850, 206269294577442542⟩, true⟩

def words03 : List Nat := [360582195400624271, 360582195955659244, 360582196428525952, 360582196736385783, 360582196929731783, 360582197123351267, 360582197282726828, 360582197332470180, 360582197333459117, 360582197300483885]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 77730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 77700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594118954324202, 360594158240587218⟩, ⟨(-931924300709916471), (-929861284511330975)⟩, true⟩

def words04 : List Nat := [360582197277151861, 360582197416527004, 360582197720792135, 360582198025262352, 360582198185702359, 360582198186812233, 360582198341661034, 360582198502485880, 360582198608767913, 360582198763737900]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 77740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 77700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360584673441586103, 360584712738426327⟩, ⟨(-197488952187027654), (-195425113556338310)⟩, true⟩

def words05 : List Nat := [360582198817863672, 360582198872099334, 360582198975466156, 360582199161869079, 360582199306574278, 360582199451475942, 360582199513537930, 360582199520878500, 360582199554102328, 360582199587700947]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 77750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 77700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593107279534738, 360593146586845023⟩, ⟨(-853399017218732644), (-851334364384947358)⟩, true⟩

def words06 : List Nat := [360582199786087464, 360582199874475753, 360582199875483957, 360582199828466714, 360582199781269962, 360582199665930042, 360582199719179827, 360582199783165650, 360582199784164213, 360582199905377832]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 77760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 77700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599388731422846, 360599428049203338⟩, ⟨(-1341896788120147994), (-1339831320966389704)⟩, true⟩

def words07 : List Nat := [360582200174370306, 360582200443681531, 360582200877779093, 360582201217161803, 360582201391425284, 360582201565766254, 360582201685866164, 360582201915149407, 360582202137524690, 360582202360140889]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 77770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 77700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597989786679370, 360598029115028812⟩, ⟨(-1233212387779321149), (-1231146098520429901)⟩, true⟩

def words08 : List Nat := [360582202456784242, 360582202457894607, 360582202485415634, 360582202582516072, 360582202609080022, 360582202652814738, 360582202653814996, 360582202585766806, 360582202579522224, 360582202784238356]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 77780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 77700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585670450542119, 360585709789365213⟩, ⟨(-274854632739540270), (-272787528681905372)⟩, true⟩

def words09 : List Nat := [360582202984585919, 360582203185141121, 360582203302921286, 360582203304031912, 360582203304698369, 360582203264284137, 360582203346911103, 360582203475720762, 360582203521778684, 360582203567996826]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 77790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 77700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 77700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk777
