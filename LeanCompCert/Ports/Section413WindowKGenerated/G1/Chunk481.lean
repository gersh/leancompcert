import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk481

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362457624964743662, 362457658290792331⟩, ⟨1324593202341999418, 1325676208231346064⟩, true⟩

def state01 : KState := ⟨⟨362478897284759668, 362478930625123726⟩, ⟨301304079805283271, 302387774339292189⟩, true⟩

def words00 : List Nat := [371285218554830564, 371285218369970842, 371285217967801384, 371285217789876798, 371285217611429392, 371285217369286706, 371285216615992676, 371285216256233446, 371285215964853165, 371285215966515107]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 48100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 48100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489796728867469, 362489830083860234⟩, ⟨(-223151261966435903), (-222066863572209817)⟩, true⟩

def words01 : List Nat := [371285215837092192, 371285215612854839, 371285215448798630, 371285215450593170, 371285215400872398, 371285215443732066, 371285215462108024, 371285215463737911, 371285215226011774, 371285215323909855]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 48110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 48100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362465199193462519, 362465232562713754⟩, ⟨960669349140976865, 961754433726905601⟩, true⟩

def words02 : List Nat := [371285215851485703, 371285215853087366, 371285215805924933, 371285215757450980, 371285215708409512, 371285215607796048, 371285215345503875, 371285215239045071, 371285215132027784, 371285214994330769]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 48120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 48100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486783785990760, 362486817169726110⟩, ⟨(-78226287996783635), (-77140506217694833)⟩, true⟩

def words03 : List Nat := [371285214595549736, 371285214612797721, 371285215011964062, 371285215013566832, 371285214914196821, 371285214742888719, 371285214732841209, 371285214734606755, 371285214747786088, 371285214782858000]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 48130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 48100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478780657137121, 362478814055342820⟩, ⟨307009855344066471, 308096333798217471⟩, true⟩

def words04 : List Nat := [371285214818452208, 371285214820054652, 371285214281149175, 371285214103910285, 371285213925861110, 371285213881226644, 371285213566013629, 371285213164056898, 371285212761480651, 371285212733095639]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 48140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 48100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362474649968483656, 362474683381153156⟩, ⟨505973620611392082, 507060795571206760⟩, true⟩

def words05 : List Nat := [371285212855745688, 371285213111946118, 371285213279480261, 371285213281083081, 371285212874456233, 371285212601581056, 371285212483042946, 371285212484656728, 371285212268925503, 371285212052157542]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 48150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 48100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472143982579843, 362472177409588506⟩, ⟨626798010577498217, 627885876185315071⟩, true⟩

def words06 : List Nat := [371285211892983511, 371285211894752061, 371285212083677364, 371285212394197644, 371285212688206451, 371285212689809579, 371285212409886597, 371285212302344017, 371285212198798658, 371285212200458038]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 48160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 48100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490907394863010, 362490940836468256⟩, ⟨(-277139612942774852), (-276051044144733148)⟩, true⟩

def words07 : List Nat := [371285211931062841, 371285211663491322, 371285211491008233, 371285211492807672, 371285211457106639, 371285211465663191, 371285211466873948, 371285211447549450, 371285211256983555, 371285211377881994]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 48170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 48100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473633684873606, 362473667140764366⟩, ⟨555169414117532047, 556258671267290649⟩, true⟩

def words08 : List Nat := [371285211678822929, 371285211680426906, 371285211408059504, 371285211137639395, 371285210866601100, 371285210640718401, 371285210200806561, 371285210190915545, 371285210180468868, 371285210171917454]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 48180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 48100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496113110909590, 362496146581308427⟩, ⟨(-528282871675544782), (-527192915309283862)⟩, true⟩

def words09 : List Nat := [371285209933492130, 371285209810363824, 371285209990565574, 371285209992169932, 371285209724487618, 371285209305033089, 371285208892986640, 371285208894755851, 371285208967139353, 371285209195874323]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 48190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 48100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 48100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk481
