import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk927A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk927B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk927A

def state06 : KState := ⟨⟨360585271111785402, 360585327803370698⟩, ⟨(-312137564012652109), (-308586532202729591)⟩, true⟩

def words05 : List Nat := [360582000104650579, 360582000168061176, 360582000347318690, 360582000585620405, 360582000758148252, 360582000930886093, 360582001013540020, 360582001045050440, 360582001082001421, 360582001119395723]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 92750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 92700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585432355539966, 360585489059755458⟩, ⟨(-327112030145957577), (-323559826693262895)⟩, true⟩

def words06 : List Nat := [360582001272449059, 360582001309849225, 360582001311064116, 360582001258756889, 360582001206208362, 360582001124961041, 360582001192657497, 360582001285355866, 360582001294792865, 360582001333777585]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 92760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 92700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360603227979654944, 360603284696553398⟩, ⟨(-1978176738835541370), (-1974623358721213990)⟩, true⟩

def words07 : List Nat := [360582001335494042, 360582001337600131, 360582001433762131, 360582001512179949, 360582001513419098, 360582001493046655, 360582001494074875, 360582001608912079, 360582001839389887, 360582002070167380]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 92770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 92700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592518408081170, 360592575137767262⟩, ⟨(-984605623253168618), (-981051056638452632)⟩, true⟩

def words08 : List Nat := [360582002221254504, 360582002318833993, 360582002429595718, 360582002540747993, 360582002544157885, 360582002545503819, 360582002509555689, 360582002410234037, 360582002326041158, 360582002441529066]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 92780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 92700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583223507289569, 360583280249638322⟩, ⟨(-122004355306942035), (-118448613662473715)⟩, true⟩

def words09 : List Nat := [360582002672594911, 360582002903936580, 360582003076790491, 360582003256626842, 360582003390902801, 360582003525545845, 360582003744218493, 360582003847338950, 360582003862322613, 360582003877469246]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 92790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 92700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 92700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk927B
