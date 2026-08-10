import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk777A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk777A
