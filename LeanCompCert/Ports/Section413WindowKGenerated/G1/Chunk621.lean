import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk621

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498232582959833, 362498289280336501⟩, ⟨(-802812133129406344), (-800433911829788866)⟩, true⟩

def state01 : KState := ⟨⟨362484247510129019, 362484304226259226⟩, ⟨65724241508513323, 68103627502462005⟩, true⟩

def words00 : List Nat := [371285400369059576, 371285400371166676, 371285400341785818, 371285400297478172, 371285400283807043, 371285400286144504, 371285400400227503, 371285400575637184, 371285400724279186, 371285400726460522]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 62100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 62100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362503561706714768, 362503618441951664⟩, ⟨(-1134015128632615180), (-1131634555828298536)⟩, true⟩

def words01 : List Nat := [371285400766860937, 371285400826007853, 371285401114097753, 371285401155770607, 371285401157402220, 371285401127759665, 371285401196902116, 371285401233160395, 371285401527848449, 371285401823484024]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 62110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 62100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483038803867961, 362483095558108818⟩, ⟨140897590353361487, 143279343780354307⟩, true⟩

def words02 : List Nat := [371285402117203179, 371285402119311169, 371285402201264472, 371285402305957473, 371285402415536459, 371285402417644453, 371285402181941802, 371285401928403342, 371285401677440391, 371285401679850012]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 62120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 62100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362469731588619481, 362469788361847697⟩, ⟨967839969494437288, 970222902703298822⟩, true⟩

def words03 : List Nat := [371285401866362798, 371285402090864287, 371285402305168557, 371285402307277636, 371285402223868466, 371285402152946952, 371285402266696551, 371285402268805012, 371285402110959656, 371285401862052128]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 62130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 62100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362498741143047930, 362498797935140573⟩, ⟨(-834919859664051461), (-832535754121772657)⟩, true⟩

def words04 : List Nat := [371285401620222004, 371285401622545511, 371285401641414901, 371285401782073135, 371285401877663898, 371285401879812603, 371285401921177244, 371285402040038468, 371285402345585042, 371285402563318370]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 62140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 62100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490997301923258, 362491054113274406⟩, ⟨(-353592186521394589), (-351206883969343457)⟩, true⟩

def words05 : List Nat := [371285402779310812, 371285402996033403, 371285403279777935, 371285403435934595, 371285403656355303, 371285403877557412, 371285404096963572, 371285404099072762, 371285404064189824, 371285404157772253]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 62150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 62100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469160924286301, 362469217754401344⟩, ⟨1003890815337942093, 1006277284352963771⟩, true⟩

def words06 : List Nat := [371285404381562395, 371285404383671657, 371285404262627460, 371285404143282729, 371285404023153240, 371285403981855626, 371285403841772391, 371285403794378501, 371285403746257239, 371285403652492915]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 62160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 62100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500141930525440, 362500198779692161⟩, ⟨(-922321535792773905), (-919933882239988045)⟩, true⟩

def words07 : List Nat := [371285403393579153, 371285403394753885, 371285403624181862, 371285403641138052, 371285403642772505, 371285403616902908, 371285403776482338, 371285403847033410, 371285404086408635, 371285404326688189]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 62170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 62100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487322462483859, 362487379330718919⟩, ⟨(-125236645031784184), (-122847805711573478)⟩, true⟩

def words08 : List Nat := [371285404511724870, 371285404513834899, 371285404353942115, 371285404326642442, 371285404346429714, 371285404348547652, 371285404191447187, 371285404030960598, 371285403965599320, 371285403999791429]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 62180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 62100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479857166932116, 362479914054172513⟩, ⟨339156528422051123, 341546549779405671⟩, true⟩

def words09 : List Nat := [371285404291761853, 371285404584623465, 371285404875684667, 371285404941193894, 371285405019905013, 371285405099608684, 371285405327822674, 371285405329933317, 371285405242149023, 371285405156258999]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 62190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 62100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 62100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk621
