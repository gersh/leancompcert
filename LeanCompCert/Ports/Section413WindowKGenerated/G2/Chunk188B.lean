import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk188A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk188B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk188A

def state06 : KState := ⟨⟨360652558116488186, 360652560170252869⟩, ⟨(-1260879444800864507), (-1260853228272817469)⟩, true⟩

def words05 : List Nat := [360585716109495030, 360585714455703071, 360585712802017084, 360585712084301175, 360585711009696594, 360585707504664561, 360585703999958453, 360585703325423166, 360585706870519409, 360585710415294340]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 18850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 18800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561501340925944, 360561503396979761⟩, ⟨456304288407769779, 456330548120152073⟩, true⟩

def words06 : List Nat := [360585712551837176, 360585712552077721, 360585712012430244, 360585712133387354, 360585712133593522, 360585709696014242, 360585704462609726, 360585697460985970, 360585690460058398, 360585686255915647]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 18860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 18800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360438380151486573, 360438382209809693⟩, ⟨2780532886562862183, 2780559189108284137⟩, true⟩

def words07 : List Nat := [360585685754685597, 360585686534905510, 360585686535122015, 360585685835944692, 360585682342861316, 360585677953127708, 360585673563786209, 360585670874115519, 360585665391355591, 360585657590588734]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 18870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 18800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360508104407839194, 360508106468435251⟩, ⟨1463955692844402581, 1463982038314287473⟩, true⟩

def words08 : List Nat := [360585649790593977, 360585643905176284, 360585639428376711, 360585636186674838, 360585632945297361, 360585627303761936, 360585622890276556, 360585617278878673, 360585611668005672, 360585606841029973]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 18880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 18800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360520110231390120, 360520112294284892⟩, ⟨1236892726155368827, 1236919115059142493⟩, true⟩

def words09 : List Nat := [360585602738744175, 360585597223141085, 360585591708079201, 360585586114069630, 360585582330067020, 360585577840723908, 360585573351829586, 360585567461590668, 360585561212731774, 360585557750108128]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 18890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 18800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 18800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk188B
