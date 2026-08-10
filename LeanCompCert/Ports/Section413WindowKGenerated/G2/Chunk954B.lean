import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk954A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk954B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk954A

def state06 : KState := ⟨⟨360585992348521942, 360586052522438045⟩, ⟨(-373252042200714173), (-369373264342582127)⟩, true⟩

def words05 : List Nat := [360582182057915301, 360582182154276846, 360582182326979441, 360582182555654741, 360582182720475858, 360582182885519375, 360582182988983397, 360582183075614648, 360582183117292694, 360582183159406623]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 95450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 95400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593232100658744, 360593292287592056⟩, ⟨(-1064394892962800548), (-1060514872414387146)⟩, true⟩

def words06 : List Nat := [360582183310809121, 360582183390315884, 360582183414937121, 360582183439697491, 360582183440855552, 360582183486988156, 360582183662660666, 360582183838596199, 360582183928849115, 360582184046634966]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 95460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 95400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360605050199900828, 360605110399923958⟩, ⟨(-2192779741222867222), (-2188898470927121692)⟩, true⟩

def words07 : List Nat := [360582184273838767, 360582184501471775, 360582184690965598, 360582184771330916, 360582184772611497, 360582184759238230, 360582184821385628, 360582184953302643, 360582185194528425, 360582185436099458]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 95470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 95400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583170004268494, 360583230217465813⟩, ⟨(-103598880379971727), (-99716352145932127)⟩, true⟩

def words08 : List Nat := [360582185617165506, 360582185689015732, 360582185870310277, 360582186052008006, 360582186172212201, 360582186183287190, 360582186184541465, 360582186111411447, 360582186038021084, 360582185968770691]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 95480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 95400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360570135380014336, 360570195606244346⟩, ⟨1141170257084451233, 1145054029874538721⟩, true⟩

def words09 : List Nat := [360582185997337336, 360582186026161279, 360582186027394192, 360582185999104309, 360582186000262644, 360582185961302532, 360582185921935994, 360582185889697947, 360582185824915204, 360582185700798007]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 95490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 95400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 95400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk954B
