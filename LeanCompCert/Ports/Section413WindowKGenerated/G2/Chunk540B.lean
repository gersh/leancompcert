import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk540A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk540B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk540A

def state06 : KState := ⟨⟨360585774364372943, 360585792815203657⟩, ⟨(-212360248925190983), (-211686311875003553)⟩, true⟩

def words05 : List Nat := [360581876889664993, 360581876660598437, 360581876480045453, 360581876852526929, 360581877055774387, 360581877259136118, 360581877259805117, 360581877244377724, 360581877048309866, 360581877121600598]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360553703598846229, 360553722056750247⟩, ⟨1521470976872771850, 1522145296342491108⟩, true⟩

def words06 : List Nat := [360581877186704233, 360581877187454872, 360581876911073958, 360581876462936491, 360581876014696820, 360581875342986225, 360581874843155063, 360581874445708651, 360581874048182154, 360581873440074503]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360578078439085715, 360578096904077115⟩, ⟨203385676581465172, 204060379301363744⟩, true⟩

def words07 : List Nat := [360581872920044191, 360581872673161571, 360581872426061211, 360581872338472272, 360581872109623100, 360581871552068965, 360581870994388323, 360581870550803253, 360581870278900479, 360581870209907392]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360561209856521403, 360561228328673147⟩, ⟨1115693079040506796, 1116368169027917256⟩, true⟩

def words08 : List Nat := [360581870140811761, 360581869897555268, 360581869769369320, 360581869876396333, 360581869877025331, 360581869824682409, 360581869431107239, 360581868761599432, 360581868091983168, 360581867414807884]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360562829752027083, 360562848231254341⟩, ⟨1028136889086125181, 1028812361822995175⟩, true⟩

def words09 : List Nat := [360581867033852777, 360581866994158125, 360581866954387710, 360581866678013818, 360581866470018149, 360581866111657270, 360581865753073959, 360581865625622754, 360581865446354686, 360581865095613362]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk540B
