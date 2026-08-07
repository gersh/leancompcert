import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk508

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362468915374527430, 362468952711379845⟩, ⟨816789696408292690, 818071089740207722⟩, true⟩

def state01 : KState := ⟨⟨362482192825722922, 362482230177761415⟩, ⟨142315989041894374, 143598153904794756⟩, true⟩

def words00 : List Nat := [371285056157144692, 371285056139521494, 371285056046219017, 371285056166810238, 371285056232129042, 371285056233859573, 371285056108059266, 371285056161966874, 371285056354983054, 371285056356740057]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 50800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 50800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471089648684189, 362471127016202451⟩, ⟨706529722460293827, 707812673927361697⟩, true⟩

def words01 : List Nat := [371285056302388453, 371285056249128349, 371285056195220297, 371285056186434796, 371285055983888848, 371285055901065268, 371285055817654978, 371285055729471098, 371285055125089540, 371285054853154977]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 50810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 50800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362460326409759589, 362460363792378544⟩, ⟨1253595059281563278, 1254878778244212764⟩, true⟩

def words02 : List Nat := [371285054692810486, 371285054694508224, 371285054292770208, 371285053889370046, 371285053485326103, 371285053164797311, 371285052671879746, 371285052298309125, 371285051924196539, 371285051551147858]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 50820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 50800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495700126478502, 362495737524459373⟩, ⟨(-544646038031952936), (-543361538146122578)⟩, true⟩

def words03 : List Nat := [371285051066625436, 371285050781580721, 371285050594947291, 371285050596675101, 371285050375762695, 371285050090239307, 371285049807623244, 371285049809495702, 371285049844758004, 371285050056900786]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 50830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 50800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479693704255269, 362479731117605847⟩, ⟨269131129372774032, 270416410732097336⟩, true⟩

def words04 : List Nat := [371285050189170780, 371285050190880915, 371285050017683763, 371285050060660805, 371285050221763274, 371285050223462143, 371285049869559549, 371285049464899010, 371285049059508521, 371285049041120736]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 50840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 50800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362466076994735702, 362466114423348632⟩, ⟨961676887801217058, 962962945330571348⟩, true⟩

def words05 : List Nat := [371285049181663450, 371285049427449517, 371285049561266093, 371285049562965756, 371285049254896711, 371285048962862494, 371285048761940176, 371285048763639769, 371285048394702675, 371285048024318561]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 50850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 50800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477993045281976, 362478030489137923⟩, ⟨355677791019168100, 356964623884570170⟩, true⟩

def words06 : List Nat := [371285047653210512, 371285047640111803, 371285047630469935, 371285047767924328, 371285047839878458, 371285047841579406, 371285047531264268, 371285047570537910, 371285047680692855, 371285047682451951]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 50860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 50800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478916973674629, 362478954433024669⟩, ⟨308709576596785944, 309997197723328262⟩, true⟩

def words07 : List Nat := [371285047545783318, 371285047405097198, 371285047507056681, 371285047575357921, 371285047626203026, 371285047677704753, 371285047726731129, 371285047728431012, 371285047262862312, 371285047145244075]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 50870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 50800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476966681031987, 362477004155548616⟩, ⟨407944663963733439, 409233056845370467⟩, true⟩

def words08 : List Nat := [371285047053453748, 371285047055165617, 371285046815000655, 371285046501426560, 371285046187230504, 371285045992396614, 371285045665043194, 371285045670521266, 371285045675802713, 371285045677593132]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 50880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 50800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496631270976770, 362496668760835717⟩, ⟨(-592830664831325728), (-591541491100314660)⟩, true⟩

def words09 : List Nat := [371285045748281488, 371285045977836547, 371285046592063545, 371285046692671962, 371285046756207701, 371285046820270327, 371285046932348945, 371285046934227681, 371285047118643174, 371285047348857558]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 50890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 50800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 50800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk508
