import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk372

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473295079807959, 362473314600796191⟩, ⟨427150391124342095, 427641145359117103⟩, true⟩

def state01 : KState := ⟨⟨362478053749231649, 362478073281017302⟩, ⟨250209221311268684, 250700377266058990⟩, true⟩

def words00 : List Nat := [371284810435639666, 371284810436863535, 371284810379908781, 371284810321354421, 371284810262364789, 371284810242039795, 371284810226061722, 371284810485655804, 371284810726073328, 371284810727329209]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 37200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 37200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362495618538655111, 362495638081408089⟩, ⟨(-403420083654880338), (-402928519549411126)⟩, true⟩

def words01 : List Nat := [371284811018524693, 371284811491394373, 371284812156498645, 371284812157713882, 371284812045712342, 371284811812774238, 371284812066821145, 371284812196747601, 371284812488451504, 371284812780649125]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 37210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 37200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362493726383281658, 362493745936982512⟩, ⟨(-333065284519337050), (-332573312879263198)⟩, true⟩

def words02 : List Nat := [371284813058690094, 371284813059904503, 371284812684135391, 371284812858149439, 371284813247735557, 371284813248970347, 371284813042044137, 371284812833291056, 371284812996758414, 371284813238078930]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 37220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 37200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466027310487108, 362466046875148386⟩, ⟨698409101492340946, 698901481243205288⟩, true⟩

def words03 : List Nat := [371284814079284742, 371284814920960041, 371284815649305778, 371284815650520065, 371284815417494689, 371284815229729249, 371284815371608047, 371284815372823009, 371284814871846707, 371284814369274144]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 37230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 37200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490130754263541, 362490150329792362⟩, ⟨(-199226949306448303), (-198734164792950225)⟩, true⟩

def words04 : List Nat := [371284813966798793, 371284813968148909, 371284814168854309, 371284814630463748, 371284815039291146, 371284815040514040, 371284814808042205, 371284814701517822, 371284815183170029, 371284815327650327]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 37240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 37200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362497645528518472, 362497665115109246⟩, ⟨(-479110780915878451), (-478617584288915709)⟩, true⟩

def words05 : List Nat := [371284815474578996, 371284815621890315, 371284816489155763, 371284817091868512, 371284817910122749, 371284818728808438, 371284819419750458, 371284819422222367, 371284819767807705, 371284820114054822]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 37250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 37200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473576976883369, 362473596574308662⟩, ⟨417822354541817448, 418315954919243212⟩, true⟩

def words06 : List Nat := [371284820756610449, 371284820757826627, 371284820595272517, 371284820431095556, 371284820266444176, 371284820230391679, 371284820091985484, 371284820349471485, 371284820505299742, 371284820506557636]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 37260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 37200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501307838359075, 362501327446776825⟩, ⟨(-615858427561244621), (-615364417438808325)⟩, true⟩

def words07 : List Nat := [371284820235063187, 371284820265345739, 371284821014764945, 371284821015980535, 371284820806267015, 371284820419738390, 371284820364588595, 371284820445517755, 371284820889132760, 371284821333275610]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 37270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 37200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478115334998252, 362478134954392356⟩, ⟨248833189802086695, 249327609178982659⟩, true⟩

def words08 : List Nat := [371284821670700493, 371284821671937162, 371284821675047693, 371284821937067419, 371284822413934008, 371284822415150014, 371284822026985182, 371284821630956541, 371284821234458763, 371284821133238669]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 37280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 37200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362464395084555772, 362464414714893259⟩, ⟨760652119813504297, 761146947323713131⟩, true⟩

def words09 : List Nat := [371284821389902732, 371284821826323816, 371284822266252004, 371284822267469420, 371284821935270908, 371284821819156815, 371284821887803901, 371284821889023655, 371284821345010570, 371284820799271911]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 37290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 37200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 37200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk372
