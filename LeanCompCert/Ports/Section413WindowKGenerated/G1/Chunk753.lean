import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk753

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362467661401146484, 362467746029148897⟩, ⟨1312108313345604647, 1316411718498615011⟩, true⟩

def state01 : KState := ⟨⟨362473285221139626, 362473369872218357⟩, ⟨888621413741152697, 892926556661488551⟩, true⟩

def words00 : List Nat := [371285228026079341, 371285227961915424, 371285227707584647, 371285227455489614, 371285227202385579, 371285227004087018, 371285226758854278, 371285226690820730, 371285226621946111, 371285226552030620]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 75300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 75300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476951209824273, 362477035884386358⟩, ⟨612512386613123641, 616819298182237437⟩, true⟩

def words01 : List Nat := [371285226396352622, 371285226396080385, 371285226423676665, 371285226426268814, 371285226222595892, 371285225991606913, 371285225759599528, 371285225577549332, 371285225306354039, 371285225200612888]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 75310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 75300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467339631576847, 362467424329547010⟩, ⟨1336478551210523962, 1340787225993376472⟩, true⟩

def words02 : List Nat := [371285225093843481, 371285224987032755, 371285224710869223, 371285224612120283, 371285224512125199, 371285224428785416, 371285224109981301, 371285223740830402, 371285223370577569, 371285223177628696]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 75320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 75300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362463870925740913, 362463955647009424⟩, ⟨1597859492580559485, 1602169922549399883⟩, true⟩

def words03 : List Nat := [371285222943112271, 371285222863680397, 371285222783397154, 371285222703846117, 371285222476956644, 371285222271339409, 371285222064358866, 371285222034238830, 371285221786789851, 371285221507409602]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 75330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 75300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474920023338717, 362475004767875485⟩, ⟨765350891373308605, 769663074484395139⟩, true⟩

def words04 : List Nat := [371285221226938341, 371285220997804226, 371285220697285642, 371285220540920551, 371285220383710411, 371285220199031821, 371285219795557258, 371285219569496817, 371285219342023952, 371285219274504343]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 75340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 75300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362480441385861707, 362480526154007854⟩, ⟨349306060369340992, 353620022567741026⟩, true⟩

def words05 : List Nat := [371285219140884037, 371285219008210182, 371285218914910382, 371285218917774455, 371285218892260780, 371285218875854578, 371285218858616601, 371285218843487261, 371285218623088852, 371285218564073775]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 75350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 75300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469830946351558, 362469915737619574⟩, ⟨1148973429830598345, 1153289134613623283⟩, true⟩

def words06 : List Nat := [371285218503594118, 371285218465506818, 371285218282200682, 371285218099816827, 371285217916467619, 371285217787802715, 371285217582821321, 371285217554805303, 371285217525926184, 371285217437694055]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 75360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 75300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489956273267117, 362490041087971879⟩, ⟨(-367996926911689602), (-363679455582132986)⟩, true⟩

def words07 : List Nat := [371285217236439519, 371285217120649844, 371285217014878050, 371285217017484790, 371285216867349511, 371285216682535090, 371285216496586218, 371285216487587955, 371285216470388312, 371285216537281624]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 75370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 75300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470025814051246, 362470110652183462⟩, ⟨1134386922411407132, 1138706159822492576⟩, true⟩

def words08 : List Nat := [371285216603312451, 371285216605906979, 371285216437307448, 371285216283878778, 371285216129115956, 371285216028729918, 371285215693236160, 371285215356865066, 371285215019469693, 371285214859105103]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 75380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 75300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362461727236227785, 362461812097749456⟩, ⟨1760147054769811600, 1764468055626407336⟩, true⟩

def words09 : List Nat := [371285214660520295, 371285214638809838, 371285214616196245, 371285214593493465, 371285214447709109, 371285214317915565, 371285214186838463, 371285214130072883, 371285213838256260, 371285213530847950]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 75390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 75300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 75300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk753
