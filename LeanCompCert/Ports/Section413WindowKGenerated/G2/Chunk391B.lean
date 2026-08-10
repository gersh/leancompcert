import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk391A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk391B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk391A

def state06 : KState := ⟨⟨360525711166343303, 360525720595927466⟩, ⟨2216109605728561722, 2216359192842900458⟩, true⟩

def words05 : List Nat := [360582327795833110, 360582327451219130, 360582327106565295, 360582326389096828, 360582325022253290, 360582323329594263, 360582321636864000, 360582320594936319, 360582319568609097, 360582318123834589]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 39150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 39100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561360616954071, 360561370051531449⟩, ⟨820076350954036196, 820326133628327020⟩, true⟩

def words06 : List Nat := [360582316679010377, 360582315884921217, 360582315741149054, 360582315994812094, 360582315995308675, 360582315629305526, 360582314614235026, 360582314039969755, 360582313465574486, 360582312766201563]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 39160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 39100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360531191490458700, 360531200930083518⟩, ⟨2002012565399621785, 2002262545807657679⟩, true⟩

def words07 : List Nat := [360582312232028105, 360582311201531533, 360582310170977284, 360582309547462117, 360582309250281441, 360582308782884947, 360582308315459097, 360582307513376287, 360582306433596820, 360582305129823377]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 39170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 39100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360567054122545966, 360567063567160858⟩, ⟨596793504281702566, 597043680225629160⟩, true⟩

def words08 : List Nat := [360582303825941065, 360582303172138444, 360582302769417657, 360582301935782687, 360582301102104624, 360582299881482309, 360582299167802729, 360582298940204571, 360582298712560089, 360582298159664702]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 39180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 39100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582395956352403, 360582405405976636⟩, ⟨(-4648617076317925), (-4398244791980945)⟩, true⟩

def words09 : List Nat := [360582298032259282, 360582298293723412, 360582298294162349, 360582298214989211, 360582297487828735, 360582296181662263, 360582294875461713, 360582293848538105, 360582293205295530, 360582293208716567]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 39190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 39100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 39100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk391B
