import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk832A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk832B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk832A

def state06 : KState := ⟨⟨362472524672648634, 362472628942044145⟩, ⟨1050693957645385854, 1056555939881394368⟩, true⟩

def words05 : List Nat := [371285319657786801, 371285319641009590, 371285319623269096, 371285319606053294, 371285319395674752, 371285319230851585, 371285319064509236, 371285319043441894, 371285318929572846, 371285318780380458]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 83250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 83200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495395601623379, 362495499896864883⟩, ⟨(-853649427315859655), (-847785293011930079)⟩, true⟩

def words06 : List Nat := [371285318629928406, 371285318611049612, 371285318548504591, 371285318581213677, 371285318588525495, 371285318591423831, 371285318516064821, 371285318552990348, 371285318732656114, 371285318857931618]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 83260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 83200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497227348482294, 362497331670077883⟩, ⟨(-1006160471691410868), (-1000294142748708286)⟩, true⟩

def words07 : List Nat := [371285318971909628, 371285319086940231, 371285319344945106, 371285319532225677, 371285319760741291, 371285319990329588, 371285320215549542, 371285320303345314, 371285320449567125, 371285320597411264]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 83270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 83200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484371116699639, 362484475464005657⟩, ⟨64558857265655593, 70427327507714761⟩, true⟩

def words08 : List Nat := [371285320800787497, 371285320812895030, 371285320815063686, 371285320797266051, 371285320801543200, 371285320804812370, 371285320859479971, 371285320944665879, 371285321028640426, 371285321031630915]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 83280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 83200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491979473249782, 362492083846691504⟩, ⟨(-569216743800624385), (-563346096587585721)⟩, true⟩

def words09 : List Nat := [371285321083159407, 371285321146318138, 371285321252653543, 371285321255542451, 371285321170019579, 371285321061999258, 371285320961724957, 371285320964908733, 371285320985100721, 371285321069574932]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 83290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 83200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 83200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk832B
