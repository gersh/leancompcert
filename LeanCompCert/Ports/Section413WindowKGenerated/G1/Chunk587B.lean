import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk587A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk587B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk587A

def state06 : KState := ⟨⟨362505635122581285, 362505685663079439⟩, ⟨(-1215275867204134434), (-1213269808556805634)⟩, true⟩

def words05 : List Nat := [371285036924512543, 371285036991496698, 371285037273468882, 371285037275455818, 371285037245399650, 371285037171840195, 371285037311753017, 371285037421611415, 371285037774357955, 371285038128004189]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 58750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 58700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489329437083610, 362489379995491070⟩, ⟨(-257081891468823806), (-255074780377825466)⟩, true⟩

def words06 : List Nat := [371285038481483056, 371285038576995144, 371285038961746375, 371285039347492265, 371285039709768032, 371285039711753791, 371285039687988116, 371285039656997895, 371285039772337890, 371285039848473361]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 58760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 58700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474486785345339, 362474537361624400⟩, ⟨615384547214871577, 617392708712100943⟩, true⟩

def words07 : List Nat := [371285040213477260, 371285040579295613, 371285040890040071, 371285040892026068, 371285040828391895, 371285040842516038, 371285041106499790, 371285041108485841, 371285040986706503, 371285040810224470]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 58770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 58700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362507570568761394, 362507621162833004⟩, ⟨(-1329433031528479779), (-1327423824096929157)⟩, true⟩

def words08 : List Nat := [371285040689851843, 371285040692040602, 371285040742995233, 371285040877082702, 371285040966636442, 371285040968677031, 371285041236394394, 371285041516760696, 371285042085694237, 371285042471807219]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 58780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 58700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492518080133720, 362492568692344048⟩, ⟨(-444399170133406669), (-442388896238500121)⟩, true⟩

def words09 : List Nat := [371285042856386340, 371285043241640608, 371285043690894508, 371285044009691582, 371285044343244020, 371285044677518412, 371285045001268976, 371285045003255993, 371285045069124950, 371285045199610277]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 58790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 58700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk587B
