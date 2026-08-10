import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk811A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk811B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk811A

def state06 : KState := ⟨⟨360582969889060316, 360583012840703018⟩, ⟨(-68887141526582102), (-66532845230881616)⟩, true⟩

def words05 : List Nat := [360582193307046183, 360582193418783959, 360582193437861416, 360582193439023131, 360582193306571419, 360582193136575356, 360582192966242449, 360582193054514790, 360582193065655673, 360582193076958968]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 81150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 81100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595645018721863, 360595687981324169⟩, ⟨(-1097586500122487084), (-1095231314291332412)⟩, true⟩

def words06 : List Nat := [360582193217306989, 360582193439658304, 360582193813291851, 360582194187138901, 360582194417493340, 360582194496500552, 360582194646059986, 360582194795958393, 360582194924629182, 360582195092062101]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 81160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 81100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360586265775679218, 360586308749375912⟩, ⟨(-336191460297096821), (-333835373882791127)⟩, true⟩

def words07 : List Nat := [360582195164299545, 360582195236677168, 360582195460410756, 360582195772991531, 360582195992110200, 360582196211409406, 360582196354706133, 360582196410459683, 360582196462072572, 360582196514075993]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 81170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 81100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587256002311406, 360587298986944126⟩, ⟨(-416606681610251354), (-414249707354160152)⟩, true⟩

def words08 : List Nat := [360582196717243998, 360582196769276624, 360582196770312052, 360582196746495976, 360582196722494950, 360582196624430299, 360582196701962267, 360582196779713002, 360582196780760068, 360582196824052252]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 81180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 81100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360596356424582661, 360596399420204013⟩, ⟨(-1155629267475672380), (-1153271400999167392)⟩, true⟩

def words09 : List Nat := [360582196882277284, 360582196940839063, 360582196994925244, 360582196996087519, 360582196898961475, 360582196672143955, 360582196445109050, 360582196393357589, 360582196569211328, 360582196745347803]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 81190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 81100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 81100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk811B
