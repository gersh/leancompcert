import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk292

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362467720962261311, 362467732749889566⟩, ⟨516611295315842550, 516843960585474790⟩, true⟩

def state01 : KState := ⟨⟨362507239196126184, 362507250992109443⟩, ⟨(-637480772844679964), (-637247863565662596)⟩, true⟩

def words00 : List Nat := [371285432846043108, 371285432912008133, 371285433526492277, 371285434141319891, 371285434312282703, 371285434313219125, 371285433436962840, 371285433585577445, 371285434905432322, 371285435653245123]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 29200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 29200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362524966962745221, 362524978767242355⟩, ⟨(-1155408257192142875), (-1155175099179499617)⟩, true⟩

def words01 : List Nat := [371285436224824496, 371285436796655193, 371285438355967181, 371285439334617157, 371285440667356679, 371285442000381337, 371285443336176856, 371285443699266087, 371285445052914919, 371285446406981601]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 29210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 29200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362503774450030676, 362503786262844004⟩, ⟨(-535962115928742601), (-535728714873179247)⟩, true⟩

def words02 : List Nat := [371285448930974817, 371285450254278773, 371285451458440356, 371285452662838362, 371285453889498690, 371285454530362547, 371285455758462607, 371285456986844808, 371285458218260874, 371285458846235843]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 29220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 29200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362531833405954966, 362531845227248740⟩, ⟨(-1356202800060281895), (-1355969151080239613)⟩, true⟩

def words03 : List Nat := [371285460643558625, 371285462441284369, 371285464737036184, 371285465706327867, 371285466481703259, 371285467257307274, 371285468766053037, 371285469865539881, 371285471452210801, 371285473039188132]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 29230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 29200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362512071632723399, 362512083462463094⟩, ⟨(-778349443868565701), (-778115547886921009)⟩, true⟩

def words04 : List Nat := [371285474591752935, 371285474592688189, 371285475751222795, 371285476915630244, 371285478433908001, 371285478981047344, 371285479531429776, 371285480082102300, 371285481220427377, 371285482130956926]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 29240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 29200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481783325062034, 362481795163225749⟩, ⟨107910780081100171, 108144922507398651⟩, true⟩

def words05 : List Nat := [371285484209123408, 371285486287518739, 371285488193857864, 371285488544363904, 371285489249175507, 371285489954409758, 371285491398052605, 371285491398988229, 371285491287195798, 371285491161944389]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 29250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 29200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482344468118506, 362482356314648386⟩, ⟨91581556087741928, 91815943351377892⟩, true⟩

def words06 : List Nat := [371285491765055035, 371285491910028426, 371285492816501999, 371285493723303182, 371285494436854245, 371285494437790256, 371285493596726786, 371285493067960932, 371285493175427306, 371285493176395957]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 29260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 29200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473964457730538, 362473976312803272⟩, ⟨337009488674938739, 337244126030508799⟩, true⟩

def words07 : List Nat := [371285493069934872, 371285492739043859, 371285493097590027, 371285493433881578, 371285494121132272, 371285494808689101, 371285495483329069, 371285495484265627, 371285494605494238, 371285494213282457]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 29270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 29200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362460773834285168, 362460785697709423⟩, ⟨723268484813232784, 723503366745184066⟩, true⟩

def words08 : List Nat := [371285493820572403, 371285493755695366, 371285492640576701, 371285491424390753, 371285490207938780, 371285489345331115, 371285487906543886, 371285487633531082, 371285487360199410, 371285487075884404]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 29280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 29200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504279889816917, 362504291761693913⟩, ⟨(-551310877138875820), (-551075747582973694)⟩, true⟩

def words09 : List Nat := [371285486233213057, 371285486128918819, 371285486505344043, 371285486506281220, 371285485595307336, 371285484493376677, 371285483452792771, 371285483453827235, 371285483714656953, 371285484357592246]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 29290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 29200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 29200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk292
