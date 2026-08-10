import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk520A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk520B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk520A

def state06 : KState := ⟨⟨360550228355898145, 360550245414387815⟩, ⟨1652477214952313026, 1653077265016516972⟩, true⟩

def words05 : List Nat := [360581999862019148, 360582000078039284, 360582000109003319, 360582000109726002, 360582000020587678, 360581999756541693, 360581999595886550, 360581999596607361, 360581999332559291, 360581998723358552]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 52050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 52000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360609369482377257, 360609386547666157⟩, ⟨(-1426778673410858864), (-1426178269344487734)⟩, true⟩

def words06 : List Nat := [360581998114016407, 360581997780623718, 360581997633627321, 360581997542940139, 360581997452209653, 360581997041278104, 360581996640878230, 360581996608969863, 360581996912401720, 360581997439153848]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 52060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 52000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593980894847434, 360593997967016784⟩, ⟨(-625465934137025064), (-624865171772474572)⟩, true⟩

def words07 : List Nat := [360581997708493976, 360581997977901821, 360581998145084101, 360581998599963694, 360581998957364463, 360581999314868698, 360581999487486924, 360581999556029707, 360581999786998196, 360582000018210646]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 52070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 52000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573894319856806, 360573911398809054⟩, ⟨420756470723978630, 421357586377054264⟩, true⟩

def words08 : List Nat := [360582000617253256, 360582000848473594, 360582000892642966, 360582000936883390, 360582000937490977, 360582000739158000, 360582000726907452, 360582000702690882, 360582000678394676, 360582000429071620]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 52080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 52000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617608255005664, 360617625340766727⟩, ⟨(-1856577186311588019), (-1855975715953280679)⟩, true⟩

def words09 : List Nat := [360582000274371014, 360582000228622941, 360582000433714102, 360582000747383900, 360582000748050017, 360582000713339006, 360582000888009463, 360582001321393986, 360582002005739791, 360582002690223489]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 52090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 52000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 52000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk520B
