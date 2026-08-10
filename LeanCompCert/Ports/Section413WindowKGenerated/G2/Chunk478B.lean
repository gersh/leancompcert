import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk478A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk478B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk478A

def state06 : KState := ⟨⟨360517527675433387, 360517541993875609⟩, ⟨3114854947651945532, 3115318018030626142⟩, true⟩

def words05 : List Nat := [360582640697995033, 360582640536566685, 360582640375070040, 360582639936462760, 360582639209263765, 360582638214440348, 360582637219465623, 360582636660087004, 360582635664562804, 360582634305159158]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 47850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 47800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360565680371149088, 360565694695804592⟩, ⟨809901426228583436, 810364794006331470⟩, true⟩

def words06 : List Nat := [360582632945667990, 360582631463574519, 360582630203743331, 360582629145240608, 360582628086730226, 360582626654131707, 360582625411276167, 360582624510342195, 360582623609252933, 360582623143559059]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 47860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 47800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360536333604890770, 360536347935835147⟩, ⟨2214913394038218266, 2215377062893801902⟩, true⟩

def words07 : List Nat := [360582622790525364, 360582622220044189, 360582621649463973, 360582621059752758, 360582620735893654, 360582620287667023, 360582619839387159, 360582619173864546, 360582618263659606, 360582617298050975]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 47870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 47800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360521560270978670, 360521574608118626⟩, ⟨2922360424315387215, 2922824389847032245⟩, true⟩

def words08 : List Nat := [360582616332242761, 360582615801612372, 360582614966688336, 360582613796250828, 360582612625754885, 360582611266401564, 360582610195850441, 360582609115038988, 360582608034207361, 360582606647998498]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 47880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 47800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580551783222943, 360580566126582363⟩, ⟨96963730387384936, 97427993799599610⟩, true⟩

def words09 : List Nat := [360582605374136456, 360582604428052487, 360582603481811735, 360582602829347330, 360582602410302900, 360582601623610985, 360582600836825769, 360582600386758924, 360582600155708049, 360582600113926823]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 47890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 47800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 47800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk478B
