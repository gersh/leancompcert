import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk660A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk660B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk660A

def state06 : KState := ⟨⟨360572147594825672, 360572175591560429⟩, ⟨710039463593807376, 711288781942099212⟩, true⟩

def words05 : List Nat := [360582941933438051, 360582942104045673, 360582942342256315, 360582942712550060, 360582942932271679, 360582943152134567, 360582943223825080, 360582943224756524, 360582943067772804, 360582942905849592]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 66050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 66000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593768750273780, 360593796755784767⟩, ⟨(-718371815430977560), (-717121917283101056)⟩, true⟩

def words06 : List Nat := [360582942743612903, 360582942736501649, 360582942737333637, 360582942601153331, 360582942464825472, 360582942241411913, 360582942454413416, 360582942675842477, 360582942783013608, 360582942948255245]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 66060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 66000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583579588700407, 360583607603016959⟩, ⟨(-45078775272261421), (-43828295296065215)⟩, true⟩

def words07 : List Nat := [360582943342019866, 360582943736045797, 360582944124589162, 360582944284773517, 360582944285633762, 360582944250575628, 360582944215345372, 360582944330110867, 360582944340908346, 360582944351926691]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 66070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 66000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593556298935070, 360593584322114360⟩, ⟨(-704476929696690357), (-703225864025866325)⟩, true⟩

def words08 : List Nat := [360582944352756863, 360582944249116042, 360582944308633032, 360582944453360962, 360582944540397718, 360582944541329462, 360582944453989107, 360582944191288048, 360582943928410368, 360582944055451337]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 66080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 66000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360568637897643155, 360568665929599897⟩, ⟨942560416532786381, 943812062349004191⟩, true⟩

def words09 : List Nat := [360582944229149281, 360582944403024751, 360582944462241044, 360582944528010056, 360582944536214179, 360582944544678319, 360582944732637772, 360582944733569643, 360582944693250106, 360582944478198218]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 66090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 66000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 66000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk660B
