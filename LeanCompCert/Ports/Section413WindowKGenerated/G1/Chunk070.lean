import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk070

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362545189352228585, 362545189948398999⟩, ⟨(-425497219626110417), (-425494393313609079)⟩, true⟩

def state01 : KState := ⟨⟨362578473104302176, 362578473702247184⟩, ⟨(-657915321422534783), (-657912482678717307)⟩, true⟩

def words00 : List Nat := [371284442836151675, 371284461828284338, 371284496314487861, 371284530790924000, 371284562495716924, 371284572784453313, 371284583525782954, 371284594264148236, 371284620280832251, 371284633667633190]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 7000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 7000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362707540326028008, 362707540925782018⟩, ⟨(-1563407775841530766), (-1563404924407504526)⟩, true⟩

def words01 : List Nat := [371284644843988434, 371284656017219472, 371284687561173265, 371284711944223505, 371284738208498975, 371284764465365528, 371284790552017705, 371284801942011271, 371284833671346440, 371284865391754458]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 7010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 7000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362554300185307975, 362554300786835591⟩, ⟨(-487187795595237184), (-487184931701188582)⟩, true⟩

def words02 : List Nat := [371284899152745763, 371284905914015833, 371284912523273714, 371284919130719061, 371284931959349461, 371284934798449881, 371284957938189553, 371284981071427214, 371284999942859315, 371285009799536318]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 7020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 7000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362727633290307086, 362727633893637580⟩, ⟨(-1706771246381382761), (-1706768369804118805)⟩, true⟩

def words03 : List Nat := [371285035998749193, 371285062190615401, 371285101173094671, 371285113252712920, 371285119223951890, 371285125193551050, 371285146527502058, 371285160762175458, 371285195204517277, 371285229637167744]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 7030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 7000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362657347888141326, 362657348493271916⟩, ⟨(-1211516728577309899), (-1211513839317904415)⟩, true⟩

def words04 : List Nat := [371285263941465073, 371285281809584042, 371285319866177656, 371285357912067529, 371285401658788729, 371285426796899398, 371285450509814647, 371285474216068778, 371285502558389274, 371285526930469774]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 7040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 7000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362505601802599652, 362505602409528204⟩, ⟨(-140576630418589374), (-140573728474427708)⟩, true⟩

def words05 : List Nat := [371285561229093869, 371285595518070048, 371285629690843423, 371285637121737700, 371285646540810366, 371285655957319718, 371285685484896364, 371285688295474503, 371285691116320892, 371285693936440196]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 7050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 7000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362582728192544612, 362582728801265820⟩, ⟨(-685406773749849326), (-685403859140351120)⟩, true⟩

def words06 : List Nat := [371285710346668144, 371285719994234061, 371285737609995565, 371285755220850360, 371285769234251679, 371285769234451981, 371285758863322551, 371285761126344439, 371285783417866753, 371285797128356706]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 7060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 7000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362553894759712181, 362553895370261287⟩, ⟨(-481281251513797955), (-481278323971837127)⟩, true⟩

def words07 : List Nat := [371285810761760898, 371285824391381419, 371285847998959603, 371285862063816694, 371285882425119752, 371285902780743030, 371285918969062519, 371285918969263267, 371285918205609222, 371285927805796969]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 7070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 7000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362429621702363905, 362429622314702148⟩, ⟨399431420161399626, 399434360379809218⟩, true⟩

def words08 : List Nat := [371285952729361573, 371285952729562387, 371285951125957731, 371285949408173388, 371285950053804301, 371285950054025383, 371285949123009929, 371285955676191882, 371285960023997590, 371285960024205648]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 7080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 7000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362535409122169745, 362535409736325917⟩, ⟨(-351430002883257827), (-351427049766454777)⟩, true⟩

def words09 : List Nat := [371285952086403489, 371285952093659812, 371285966302390976, 371285966302592216, 371285954081753618, 371285935696672556, 371285917316689861, 371285914331966131, 371285912968529152, 371285919939147146]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 7090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 7000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 7000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk070
