import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk304

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362466421199637312, 362466434019418069⟩, ⟨582226487029928626, 582489915057486214⟩, true⟩

def state01 : KState := ⟨⟨362478032054884998, 362478044883411338⟩, ⟨229230563273404405, 229494257211411115⟩, true⟩

def words00 : List Nat := [371285594242290924, 371285593861786823, 371285593096172655, 371285593254021867, 371285593254777160, 371285593235644048, 371285592054200381, 371285591583896353, 371285591553141708, 371285591554151602]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 30400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 30400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362467322895695899, 362467335733108739⟩, ⟨554997860062989060, 555261824284064606⟩, true⟩

def words01 : List Nat := [371285591306733132, 371285591089364778, 371285591339572708, 371285591340648360, 371285591312803175, 371285591177961084, 371285591042786808, 371285590909984659, 371285589514869190, 371285588916024060]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 30410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 30400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478797506284098, 362478810352402332⟩, ⟨205964516459327663, 206228745543718695⟩, true⟩

def words02 : List Nat := [371285588519407744, 371285588520401697, 371285587999940696, 371285587482277344, 371285586964267445, 371285586769194469, 371285586714754210, 371285587227121791, 371285587503723531, 371285587504736993]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 30420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 30400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362516802456026268, 362516815310983829⟩, ⟨(-950694554399488467), (-950430056289443413)⟩, true⟩

def words03 : List Nat := [371285588137522232, 371285588993475055, 371285590559414673, 371285590688783901, 371285590689540164, 371285590642668222, 371285591107026802, 371285591219846203, 371285592246268419, 371285593273064923]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 30430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 30400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362498451022803922, 362498463886591568⟩, ⟨(-392134593820256310), (-391869826878461562)⟩, true⟩

def words04 : List Nat := [371285594322325582, 371285594323303471, 371285594465031289, 371285594761635891, 371285595385797713, 371285595386779665, 371285594985449463, 371285594497794341, 371285594597217245, 371285595020975383]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 30440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 30400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362452176509672233, 362452189382244834⟩, ⟨1017338842939131061, 1017603877427870171⟩, true⟩

def words05 : List Nat := [371285596269597587, 371285597518526554, 371285598769609470, 371285598770586990, 371285598730679695, 371285598875747088, 371285599260271658, 371285599261249380, 371285598353132880, 371285597257406616]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 30450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 30400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494909800478610, 362494922681800239⟩, ⟨(-284507621481221071), (-284242320452289617)⟩, true⟩

def words06 : List Nat := [371285596161328168, 371285596018631345, 371285595468427930, 371285595602387462, 371285595603151523, 371285595586809093, 371285594136655125, 371285593761705131, 371285594084770423, 371285594391936031]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 30460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 30400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499832995653538, 362499845885905942⟩, ⟨(-434549365583154199), (-434283792388571255)⟩, true⟩

def words07 : List Nat := [371285594476294209, 371285594560977018, 371285595532786384, 371285595973913447, 371285596512951500, 371285597052319240, 371285597594296365, 371285597595291793, 371285597728764160, 371285598197431530]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 30470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 30400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362451674697405166, 362451687596359400⟩, ⟨1033516686541775340, 1033782525014214976⟩, true⟩

def words08 : List Nat := [371285598862743587, 371285598863721974, 371285598097025453, 371285597344135452, 371285596590945444, 371285595817735596, 371285594504906418, 371285594076312021, 371285593647407309, 371285593221974822]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 30480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 30400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362512181981663106, 362512194889478821⟩, ⟨(-811588284896732800), (-811322176194728774)⟩, true⟩

def words09 : List Nat := [371285592110651515, 371285592072739533, 371285593067926519, 371285593068905378, 371285592829787591, 371285592484103328, 371285592863845998, 371285593288439012, 371285594161299151, 371285595034516862]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 30490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 30400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 30400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk304
