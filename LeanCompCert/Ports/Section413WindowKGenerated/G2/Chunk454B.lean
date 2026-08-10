import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk454A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk454B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk454A

def state06 : KState := ⟨⟨360576212918413772, 360576225782083333⟩, ⟨320537473860899066, 320932648402831392⟩, true⟩

def words05 : List Nat := [360583286569909036, 360583286930559061, 360583287035462787, 360583287036085343, 360583286658133515, 360583286157336075, 360583285656378360, 360583285607281027, 360583285607840816, 360583285453187663]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 45450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 45400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587144332492763, 360587157202036452⟩, ⟨(-176483131513991219), (-176087689904304039)⟩, true⟩

def words06 : List Nat := [360583285298402809, 360583285453872218, 360583285727709794, 360583286001651154, 360583286002235158, 360583285815277263, 360583285277603621, 360583284952501068, 360583284627223656, 360583284674713449]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 45460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 45400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360549610977407404, 360549623852891657⟩, ⟨1530449863774668258, 1530845575530091598⟩, true⟩

def words07 : List Nat := [360583284675269081, 360583284458306936, 360583284299076444, 360583284763294247, 360583284925145291, 360583285087088813, 360583285087649306, 360583284957750600, 360583284345497694, 360583283606091528]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 45470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 45400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360539985682500406, 360539998563850015⟩, ⟨1968252323160391850, 1968648301701609348⟩, true⟩

def words08 : List Nat := [360583282866511434, 360583282609716828, 360583281870658310, 360583280889134290, 360583279907555283, 360583278606994410, 360583277692751735, 360583276918767087, 360583276144748598, 360583275070812021]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 45480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 45400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360581121119085718, 360581134006327025⟩, ⟨96717854641401513, 97114101223801887⟩, true⟩

def words09 : List Nat := [360583274119995717, 360583273651844548, 360583273183538447, 360583272551749043, 360583271822162898, 360583270671984972, 360583269521733986, 360583268854067198, 360583268428428484, 360583268382178098]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 45490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 45400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 45400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk454B
