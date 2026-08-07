import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk469

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482082587932023, 362482114206515815⟩, ⟨151604338200941362, 152606234733088196⟩, true⟩

def state01 : KState := ⟨⟨362486550181713663, 362486581814235283⟩, ⟨(-57874490292833311), (-56871940004976497)⟩, true⟩

def words00 : List Nat := [371285368386835834, 371285368545292392, 371285368904424142, 371285369264203556, 371285369524735209, 371285369526294199, 371285369268824403, 371285369201931892, 371285369449799558, 371285369477256644]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 46900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 46900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488897592668361, 362488929239408318⟩, ⟨(-167978937023888866), (-166975719684136684)⟩, true⟩

def words01 : List Nat := [371285369484818479, 371285369492924765, 371285369878338568, 371285370101780016, 371285370338487396, 371285370575759969, 371285370804251599, 371285370805810554, 371285370505153013, 371285370582949928]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 46910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 46900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486016349421061, 362486048010075652⟩, ⟨(-32805393810870053), (-31801523525488507)⟩, true⟩

def words02 : List Nat := [371285370849729920, 371285370851290339, 371285370625498008, 371285370401120933, 371285370176172863, 371285370089014239, 371285370025536205, 371285370198097839, 371285370371043431, 371285370387107348]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 46920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 46900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362508977119323383, 362509008794029499⟩, ⟨(-1110429197715893587), (-1109424667918358385)⟩, true⟩

def words03 : List Nat := [371285370803775573, 371285371221215491, 371285372090921850, 371285372451471624, 371285372680810097, 371285372910604676, 371285373236286830, 371285373335261383, 371285373839844881, 371285374345084689]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 46930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 46900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474072841074237, 362474104529875874⟩, ⟨528150613586688120, 529155805098977750⟩, true⟩

def words04 : List Nat := [371285374850678918, 371285374986627176, 371285375302142429, 371285375618484373, 371285375985483804, 371285375987043447, 371285375749974708, 371285375514427857, 371285375278281146, 371285375154052637]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 46940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 46900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362463761699307755, 362463793402171216⟩, ⟨1012397292025042381, 1013403143810975501⟩, true⟩

def words05 : List Nat := [371285375017047462, 371285375120734776, 371285375165638964, 371285375167202974, 371285374747585386, 371285374467119236, 371285374356135167, 371285374357695632, 371285373995040918, 371285373537260888]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 46950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 46900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481963525437116, 362481995242284151⟩, ⟨157565610671500332, 158572119196416054⟩, true⟩

def words06 : List Nat := [371285373078786723, 371285373021437033, 371285372738538659, 371285372645880426, 371285372552756087, 371285372395123497, 371285371750306309, 371285371491498634, 371285371270418715, 371285371272073302]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 46960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 46900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483984563261382, 362484016294305524⟩, ⟨62650850732787287, 63658026167235691⟩, true⟩

def words07 : List Nat := [371285371201379778, 371285371073821830, 371285371225740711, 371285371280405563, 371285371471989037, 371285371664181989, 371285371761932034, 371285371763493137, 371285371323897689, 371285371296991077]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 46970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 46900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474653154457710, 362474684899402012⟩, ⟨501116371641503891, 502124200178353161⟩, true⟩

def words08 : List Nat := [371285371475093397, 371285371476661914, 371285371267895287, 371285371060778446, 371285370853030503, 371285370784154891, 371285370584223986, 371285370652682766, 371285370664973363, 371285370666590315]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 46980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 46900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504758762353436, 362504790521451463⟩, ⟨(-913741394763449201), (-912732901073180137)⟩, true⟩

def words09 : List Nat := [371285370440268586, 371285370384822781, 371285370723029119, 371285370724590559, 371285370517495065, 371285370268181139, 371285370219034029, 371285370256464768, 371285370670722200, 371285371085671944]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 46990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 46900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 46900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk469
