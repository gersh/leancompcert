import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk550

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360540972903951975, 360540992028697120⟩, ⟨2241792271836542638, 2242502958391420826⟩, true⟩

def state01 : KState := ⟨⟨360596297240813343, 360596316372767809⟩, ⟨(-801329125093824337), (-800618041989660607)⟩, true⟩

def words00 : List Nat := [360581764069067090, 360581763658491860, 360581763442874765, 360581763326135889, 360581763209343250, 360581762822341886, 360581762443523912, 360581762294952259, 360581762326493849, 360581762591851453]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 55000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 55000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360565471427843530, 360565490567091614⟩, ⟨894526865666851241, 895238350029068489⟩, true⟩

def words01 : List Nat := [360581762607906153, 360581762624041232, 360581762624670874, 360581762621569677, 360581762632869754, 360581762644298938, 360581762644986685, 360581762490229987, 360581762006071041, 360581761711221550]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 55010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 55000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570754830873881, 360570773977324627⟩, ⟨603900441356880571, 604612322045369005⟩, true⟩

def words02 : List Nat := [360581761450014567, 360581761582191439, 360581761582872893, 360581761550160059, 360581761517323305, 360581761322070209, 360581761294477378, 360581761256637504, 360581761218720721, 360581760935748130]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 55020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 55000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603138221132189, 360603157374796299⟩, ⟨(-1178340802884984527), (-1177628525207640893)⟩, true⟩

def words03 : List Nat := [360581760805422982, 360581760874970069, 360581760994583240, 360581761122520083, 360581761123232143, 360581760969462905, 360581760883275130, 360581761117544021, 360581761506903626, 360581761896421858]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 55030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 55000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360609038803879177, 360609057964844114⟩, ⟨(-1503293068851068082), (-1502580389301388270)⟩, true⟩

def words04 : List Nat := [360581762030026733, 360581762214548140, 360581762545209057, 360581762876094695, 360581763073099153, 360581763158826916, 360581763159508872, 360581763041569527, 360581763134010292, 360581763630693938]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 55040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 55000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360572766098410091, 360572785266575237⟩, ⟨493790638556672245, 494503714514634475⟩, true⟩

def words05 : List Nat := [360581764456337674, 360581765282098010, 360581765940523389, 360581766270185365, 360581766271990223, 360581766273980255, 360581766604917981, 360581766607198059, 360581766607879947, 360581766445552982]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 55050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 55000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360602562636665976, 360602581812070441⟩, ⟨(-1146885881891327876), (-1146172407301913720)⟩, true⟩

def words06 : List Nat := [360581766449079699, 360581766891196161, 360581767296478799, 360581767701891347, 360581767825992457, 360581767901250531, 360581768204242620, 360581768507452098, 360581768802247708, 360581769180970554]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 55060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 55000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602243985635221, 360602263168333347⟩, ⟨(-1129325517434198422), (-1128611641147347780)⟩, true⟩

def words07 : List Nat := [360581769351732766, 360581769522565361, 360581770022238380, 360581770729928069, 360581771350510188, 360581771971207459, 360581772343539118, 360581772387383125, 360581772760020669, 360581773132910110]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 55070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 55000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579118311076735, 360579137500996016⟩, ⟨144395232662145167, 145109506726710305⟩, true⟩

def words08 : List Nat := [360581773444264173, 360581773445029888, 360581773427914472, 360581773128027671, 360581772828027555, 360581772352485971, 360581772042235720, 360581771931943824, 360581771821573623, 360581771545409280]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 55080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 55000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588511878160251, 360588531075307864⟩, ⟨(-373094720674358853), (-372380048364890215)⟩, true⟩

def words09 : List Nat := [360581771698269226, 360581771899159128, 360581772288755581, 360581772616718792, 360581772663924271, 360581772711187869, 360581772711819682, 360581772692640482, 360581772815920693, 360581772939369045]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 55090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 55000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 55000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk550
