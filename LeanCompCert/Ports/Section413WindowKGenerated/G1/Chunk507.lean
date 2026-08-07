import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk507

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488525705659201, 362488562889825251⟩, ⟨(-178832456526135244), (-177558812051960712)⟩, true⟩

def state01 : KState := ⟨⟨362481120320557516, 362481157519823519⟩, ⟨196624495316535868, 197898905438436638⟩, true⟩

def words00 : List Nat := [371285061044386178, 371285061046079886, 371285060799925757, 371285060554686280, 371285060308787131, 371285060182983179, 371285059936009499, 371285060008016841, 371285060079790694, 371285060081555691]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 50700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 50700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489576002183462, 362489613216763066⟩, ⟨(-232252479774528031), (-230977293022622623)⟩, true⟩

def words01 : List Nat := [371285060080380851, 371285060157045539, 371285060428739753, 371285060430433754, 371285060184449875, 371285059822838538, 371285059460568006, 371285059394368743, 371285059246125095, 371285059337836732]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 50710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 50700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478364043348606, 362478401273234333⟩, ⟨336452382634407734, 337728345791287638⟩, true⟩

def words02 : List Nat := [371285059339113957, 371285059340757799, 371285059084106907, 371285059151313712, 371285059333353703, 371285059335056172, 371285059146098119, 371285058924676461, 371285058702575581, 371285058642558033]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 50720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 50700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362470642538919098, 362470679784054174⟩, ⟨728269209639908080, 729545946473431000⟩, true⟩

def words03 : List Nat := [371285058704729912, 371285058898808070, 371285059093695076, 371285059095390002, 371285058772755482, 371285058549413920, 371285058463536212, 371285058465233674, 371285058188252994, 371285057906767486]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 50730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 50700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477126296839272, 362477163557158120⟩, ⟨399272309792926535, 400549817130052587⟩, true⟩

def words04 : List Nat := [371285057729102213, 371285057730987312, 371285057643986189, 371285057605505532, 371285057566488464, 371285057446122937, 371285056808021168, 371285056499579792, 371285056190294498, 371285056164392210]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 50740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 50700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362487376137269631, 362487413413063521⟩, ⟨(-120923539215059494), (-119645246444345356)⟩, true⟩

def words05 : List Nat := [371285056010155870, 371285055854200575, 371285055927408689, 371285056023795606, 371285056238662702, 371285056454154112, 371285056594658739, 371285056596355239, 371285056333573411, 371285056382145211]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 50750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 50700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477852975769951, 362477890266671274⟩, ⟨362548072981508277, 363827132683833243⟩, true⟩

def words06 : List Nat := [371285056704199844, 371285056705900326, 371285056630546974, 371285056556186799, 371285056481177636, 371285056398347089, 371285056229708887, 371285056340412190, 371285056448344537, 371285056450100147]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 50760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 50700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501618874625870, 362501656180865657⟩, ⟨(-844170083417931057), (-842890244903879365)⟩, true⟩

def words07 : List Nat := [371285056329988011, 371285056351861167, 371285056760255017, 371285056761951743, 371285056714499127, 371285056613537395, 371285056796386776, 371285056988295669, 371285057316335841, 371285057645096297]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 50770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 50700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480055501438347, 362480092822967596⟩, ⟨250855956547201532, 252136571538396998⟩, true⟩

def words08 : List Nat := [371285057973583012, 371285057975279484, 371285057918704751, 371285058052266444, 371285058199908068, 371285058201604920, 371285057890679715, 371285057504410225, 371285057117482495, 371285057118528502]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 50780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 50700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468915374527430, 362468952711379845⟩, ⟨816789696408292690, 818071089740207722⟩, true⟩

def words09 : List Nat := [371285057180992967, 371285057341921394, 371285057502657221, 371285057504354217, 371285057196167187, 371285057007908553, 371285056975351218, 371285056977059643, 371285056788067542, 371285056472988905]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 50790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 50700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 50700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk507
