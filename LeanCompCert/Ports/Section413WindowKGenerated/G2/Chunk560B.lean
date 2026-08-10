import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk560A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk560B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk560A

def state06 : KState := ⟨⟨360595940506709700, 360595960406402756⟩, ⟨(-794155429461965806), (-793401708709888948)⟩, true⟩

def words05 : List Nat := [360581807765918851, 360581807778612734, 360581808108839934, 360581808121775824, 360581808122495963, 360581807823978469, 360581807525299942, 360581807428479667, 360581807681572185, 360581807934832326]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 56050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 56000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561968393341782, 360561988300486516⟩, ⟨1110357580379699805, 1111111718909252571⟩, true⟩

def words06 : List Nat := [360581808028240439, 360581808029021030, 360581807805022033, 360581807573154542, 360581807341088548, 360581807028721918, 360581806667862319, 360581806067385951, 360581805466785909, 360581804810543753]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 56060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 56000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360541677655562388, 360541697570051896⟩, ⟨2248239827041713198, 2248994377430197226⟩, true⟩

def words07 : List Nat := [360581804457757105, 360581804319972151, 360581804182106714, 360581803885164190, 360581803508286199, 360581803048844847, 360581802589202024, 360581802121718125, 360581801607786339, 360581800893472549]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 56070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 56000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580868458323751, 360580888380184508⟩, ⟨50262744506351870, 51017708310971108⟩, true⟩

def words08 : List Nat := [360581800179007492, 360581799782206316, 360581799587679033, 360581799498004356, 360581799408258597, 360581799048603473, 360581798523471163, 360581798315941944, 360581798108185299, 360581797948883224]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 56080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 56000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590661321626710, 360590681250936512⟩, ⟨(-499128513909934904), (-498373132252242670)⟩, true⟩

def words09 : List Nat := [360581797933375173, 360581797671875166, 360581797465257589, 360581797680445622, 360581797719864559, 360581797759406375, 360581797760109772, 360581797593388520, 360581797593490068, 360581797752741253]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 56090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 56000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 56000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk560B
