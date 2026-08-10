import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk448A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk448B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk448A

def state06 : KState := ⟨⟨360588749221265395, 360588761733955624⟩, ⟨(-250224607697821677), (-249845283616912687)⟩, true⟩

def words05 : List Nat := [360583189024638938, 360583189881448811, 360583190488974592, 360583190822379800, 360583191029264511, 360583191236320388, 360583191735611913, 360583192164043499, 360583192288745803, 360583192413529934]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 44850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 44800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598823166503953, 360598835684993388⟩, ⟨(-702237988341742239), (-701858404079151415)⟩, true⟩

def words06 : List Nat := [360583192931185805, 360583193700114382, 360583194055884479, 360583194411743485, 360583194412314689, 360583194342124852, 360583193776212949, 360583193706595043, 360583193642803058, 360583193992049635]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 44860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 44800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360598518524792180, 360598531049129174⟩, ⟨(-688606597159562558), (-688226750488309496)⟩, true⟩

def words07 : List Nat := [360583194092304318, 360583194192621764, 360583194520687397, 360583195104261065, 360583195543637777, 360583195983097303, 360583196039091147, 360583196039706479, 360583196227779013, 360583196570162834]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 44870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 44800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595813560353198, 360595826090465332⟩, ⟨(-567273157091821305), (-566893051202469609)⟩, true⟩

def words08 : List Nat := [360583197193330253, 360583197321298252, 360583197321850348, 360583197199711396, 360583197077467216, 360583196746028674, 360583197079520468, 360583197494438083, 360583197596819947, 360583197878770283]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 44880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 44800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590552569730641, 360590565105649037⟩, ⟨(-331215639440317481), (-330835272879542097)⟩, true⟩

def words09 : List Nat := [360583197879279066, 360583197864685215, 360583198330178095, 360583198330792299, 360583198316575293, 360583197848188455, 360583197379706421, 360583196836870736, 360583196836128713, 360583197000865635]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 44890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 44800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 44800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk448B
