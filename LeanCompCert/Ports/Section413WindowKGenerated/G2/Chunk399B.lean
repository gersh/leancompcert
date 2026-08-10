import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk399A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk399B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk399A

def state06 : KState := ⟨⟨360575944732432317, 360575954567376640⟩, ⟨265319013040231196, 265584636772381266⟩, true⟩

def words05 : List Nat := [360582599722083085, 360582599528441114, 360582599765671951, 360582600511088666, 360582600978983649, 360582601446952669, 360582601532496974, 360582601533038133, 360582600995261711, 360582600829558132]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 39950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 39900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595791754458167, 360595801594506236⟩, ⟨(-527892302817854087), (-527626475114307753)⟩, true⟩

def words06 : List Nat := [360582600960601814, 360582601381308187, 360582601381802005, 360582601221380725, 360582601060879207, 360582600742041553, 360582600939745138, 360582601143374831, 360582601143861624, 360582601362460145]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 39960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 39900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360660165347000157, 360660175192156752⟩, ⟨(-3101221295432971644), (-3100955263516224590)⟩, true⟩

def words07 : List Nat := [360582602317652921, 360582603272956467, 360582604658801962, 360582606243512327, 360582607258244265, 360582608272965720, 360582609271642294, 360582610588153989, 360582612528676982, 360582614469225455]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 39970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 39900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360639785925213113, 360639795775525385⟩, ⟨(-2286580833554045529), (-2286314595488094503)⟩, true⟩

def words08 : List Nat := [360582616096957229, 360582617101972719, 360582618730958484, 360582620360033380, 360582621576630253, 360582622170619582, 360582622444753866, 360582622718931176, 360582623616980644, 360582625047224315]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 39980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 39900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360566362327230767, 360566372182649880⟩, ⟨649972773397480568, 650239215711725324⟩, true⟩

def words09 : List Nat := [360582626271457146, 360582627495724490, 360582628407426709, 360582628696734066, 360582628697188416, 360582628681243892, 360582628665133001, 360582628609753668, 360582628568890893, 360582628163042674]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 39990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 39900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 39900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk399B
