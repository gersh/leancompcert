import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk636

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362469132151703960, 362469191733049293⟩, ⟨1028995216243255394, 1031554704590699448⟩, true⟩

def state01 : KState := ⟨⟨362474994168252571, 362475053768860715⟩, ⟨656214104293396234, 658774817857249226⟩, true⟩

def words00 : List Nat := [371285410893091777, 371285410887616859, 371285410751980831, 371285410595887345, 371285410438990643, 371285410357905845, 371285410193466375, 371285410236519663, 371285410238172046, 371285410235105917]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 63600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 63600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362503742627927323, 362503802248065121⟩, ⟨(-1172626646852416490), (-1170064690911113524)⟩, true⟩

def words01 : List Nat := [371285410158213687, 371285410245258726, 371285410457242569, 371285410459410630, 371285410418537398, 371285410340550133, 371285410428430354, 371285410495012276, 371285410785566881, 371285411077053803]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 63610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 63600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492249698079895, 362492309337769217⟩, ⟨(-441452127659874125), (-438888927752235733)⟩, true⟩

def words02 : List Nat := [371285411368841290, 371285411425919909, 371285411551086131, 371285411677379663, 371285411877351086, 371285411879515634, 371285411812860878, 371285411733744866, 371285411819476941, 371285411930408776]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 63620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 63600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362465628263879602, 362465687923043020⟩, ⟨1252649033153902480, 1255213472298346494⟩, true⟩

def words03 : List Nat := [371285412147538750, 371285412365563874, 371285412582028440, 371285412584191278, 371285412471427947, 371285412345443023, 371285412218390647, 371285412193994755, 371285411886591772, 371285411579113076]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 63630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 63600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490576542189792, 362490636220741938⟩, ⟨(-335183886787205713), (-332618213650745019)⟩, true⟩

def words04 : List Nat := [371285411270662064, 371285411140786176, 371285410887024551, 371285410838498771, 371285410789280358, 371285410702804109, 371285410400333223, 371285410346062750, 371285410480652803, 371285410564999676]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 63640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 63600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362496051891456444, 362496111589689974⟩, ⟨(-683729310220608342), (-681162384261282338)⟩, true⟩

def words05 : List Nat := [371285410599584290, 371285410634849658, 371285410880154222, 371285411008048664, 371285411183860052, 371285411360512597, 371285411488085792, 371285411490286957, 371285411580998775, 371285411751731707]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 63650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 63600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480120236988990, 362480179954491598⟩, ⟨330557267615433291, 333125420344123101⟩, true⟩

def words06 : List Nat := [371285412040408865, 371285412042572616, 371285412027151478, 371285412011695292, 371285411995410245, 371285411946820099, 371285411857674705, 371285411938145614, 371285412014766956, 371285412017006820]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 63660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 63600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500014902259021, 362500074639370532⟩, ⟨(-936170115673703740), (-933600714347804894)⟩, true⟩

def words07 : List Nat := [371285412100983674, 371285412268314538, 371285412621639144, 371285412789199232, 371285412923566758, 371285413058566475, 371285413385211384, 371285413589935650, 371285413821669669, 371285414054355413]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 63670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 63600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362499354407737822, 362499414164378428⟩, ⟨(-894166137403194724), (-891595492365246110)⟩, true⟩

def words08 : List Nat := [371285414285376645, 371285414287546882, 371285414444560166, 371285414625766802, 371285414865303122, 371285414900938415, 371285414909771532, 371285414919349067, 371285415174730527, 371285415397011528]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 63680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 63600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488481409412668, 362488541185546409⟩, ⟨(-201537323572852626), (-198965436918594632)⟩, true⟩

def words09 : List Nat := [371285415864972830, 371285416333780352, 371285416750524549, 371285416839228613, 371285417001846234, 371285417165558063, 371285417574767661, 371285417656172844, 371285417706830926, 371285417758333044]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 63690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 63600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 63600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk636
