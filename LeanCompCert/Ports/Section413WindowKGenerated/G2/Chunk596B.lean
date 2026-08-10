import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk596A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk596B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk596A

def state06 : KState := ⟨⟨360618294801278327, 360618317451340870⟩, ⟨(-2161310133100558764), (-2160397221233688288)⟩, true⟩

def words05 : List Nat := [360582103180087612, 360582103682632858, 360582104033630333, 360582104390675128, 360582104469525461, 360582104548438067, 360582104695392716, 360582105022149756, 360582105629804251, 360582106237629506]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 59650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 59600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360616977102760448, 360616999760790147⟩, ⟨(-2082842072467542300), (-2081928685243214304)⟩, true⟩

def words06 : List Nat := [360582106626419862, 360582106886176559, 360582107426888601, 360582107967833734, 360582108436553860, 360582108625637581, 360582108673224570, 360582108720915771, 360582109049494093, 360582109635180669]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 59660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 59600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360584595796938065, 360584618462816231⟩, ⟨(-150404946813940270), (-149491091231703452)⟩, true⟩

def words07 : List Nat := [360582110501607433, 360582111368165208, 360582112093246096, 360582112538693117, 360582112728262585, 360582112918028719, 360582113322119172, 360582113541693891, 360582113584418286, 360582113627253293]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 59670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 59600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360607602398072218, 360607625071841780⟩, ⟨(-1523507177514987457), (-1522592850935940969)⟩, true⟩

def words08 : List Nat := [360582113832931043, 360582114275656200, 360582114800488961, 360582115325461319, 360582115586350354, 360582115804727372, 360582116115994835, 360582116427503660, 360582116730368626, 360582117158572846]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 59680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 59600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360614662549343210, 360614685231059728⟩, ⟨(-1944976971976457501), (-1944062171004219241)⟩, true⟩

def words09 : List Nat := [360582117428666795, 360582117698842981, 360582118249656152, 360582118939924054, 360582119558109928, 360582120176430359, 360582120562941803, 360582120828503549, 360582121374645761, 360582121921048100]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 59690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 59600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 59600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk596B
