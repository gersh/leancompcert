import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk788A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk788B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk788A

def state06 : KState := ⟨⟨362491096276017097, 362491189426737910⟩, ⟨(-475854932749737945), (-470894470295445447)⟩, true⟩

def words05 : List Nat := [371285218031050694, 371285218026239846, 371285218172686438, 371285218175409824, 371285218134570591, 371285218055639805, 371285218054339516, 371285218074625607, 371285218152206356, 371285218230959320]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 78850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 78800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478185842192357, 362478279017513205⟩, ⟨542323407743070767, 547285810279787221⟩, true⟩

def words06 : List Nat := [371285218293792954, 371285218296565121, 371285218295769713, 371285218348588029, 371285218449437323, 371285218452161852, 371285218367584929, 371285218267198492, 371285218165767060, 371285218104748907]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 78860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 78800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470034035538766, 362470127235409475⟩, ⟨1185337188718451451, 1190301527625289849⟩, true⟩

def words07 : List Nat := [371285218036951770, 371285218058258669, 371285218068595969, 371285218071320259, 371285217887140401, 371285217752701505, 371285217639643576, 371285217642367772, 371285217453112359, 371285217264917910]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 78870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 78800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473575109045455, 362473668333322981⟩, ⟨905966546328614842, 910932810568689652⟩, true⟩

def words08 : List Nat := [371285217075477252, 371285216940440288, 371285216723958501, 371285216555456224, 371285216386137529, 371285216193197137, 371285215785287065, 371285215539392650, 371285215292060202, 371285215206317895]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 78880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 78800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476780417093158, 362476873666157548⟩, ⟨653106617087490624, 658074836889384100⟩, true⟩

def words09 : List Nat := [371285215061989494, 371285214918563625, 371285214788207903, 371285214791241666, 371285214728932988, 371285214709397343, 371285214688957253, 371285214637278864, 371285214387493357, 371285214285129531]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 78890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 78800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 78800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk788B
