import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk305A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk305B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk305A

def state06 : KState := ⟨⟨360621227802226495, 360621233428236730⟩, ⟨(-1155811324499762418), (-1155695053055078354)⟩, true⟩

def words05 : List Nat := [360583420183776828, 360583419572583048, 360583419416615764, 360583419417021491, 360583418806107513, 360583417105930091, 360583415405786506, 360583414943472267, 360583416181316391, 360583417419171089]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 30550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 30500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360612742006279930, 360612747636160558⟩, ⟨(-896498375997300556), (-896381986254590538)⟩, true⟩

def words06 : List Nat := [360583417993802377, 360583419013302744, 360583420344620354, 360583421675972437, 360583422736882376, 360583424056175533, 360583424684129471, 360583425312086101, 360583425359405744, 360583426319021617]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 30560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 30500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360549209916263289, 360549215549967018⟩, ⟨1046076955337280976, 1046193461971357774⟩, true⟩

def words07 : List Nat := [360583427745080783, 360583429171123549, 360583429935649582, 360583429936055622, 360583429634762923, 360583429049252643, 360583428943132684, 360583428943538737, 360583428357744855, 360583427239370922]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 30570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 30500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585886705609088, 360585892343149919⟩, ⟨(-75780687045725477), (-75664063054101327)⟩, true⟩

def words08 : List Nat := [360583426120975821, 360583425834278803, 360583425834613871, 360583425466659509, 360583425098697545, 360583423815602739, 360583421949018337, 360583420835946451, 360583419722830212, 360583418933877450]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 30580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 30500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360553519282698303, 360553524924109304⟩, ⟨914551970731088587, 914668713130080263⟩, true⟩

def words09 : List Nat := [360583418934245486, 360583418158695833, 360583417671503305, 360583418498376172, 360583418809454296, 360583419120578042, 360583419120946686, 360583418609965974, 360583417034922650, 360583416058525320]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 30590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 30500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 30500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk305B
