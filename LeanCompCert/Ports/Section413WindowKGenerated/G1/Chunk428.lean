import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk428

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362531643085980345, 362531669222881807⟩, ⟨(-1984817223752635639), (-1984061366359979833)⟩, true⟩

def state01 : KState := ⟨⟨362493349083765997, 362493375233387505⟩, ⟨(-345706315264034985), (-344949913387577747)⟩, true⟩

def words00 : List Nat := [371285314710582070, 371285314961617476, 371285315598231154, 371285316235545997, 371285316900505428, 371285317010839812, 371285317107937999, 371285317205517722, 371285317537001680, 371285317726826398]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 42800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 42800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473231574549448, 362473257736879976⟩, ⟨515727855607133829, 516484801621638621⟩, true⟩

def words01 : List Nat := [371285318365290102, 371285319004320548, 371285319588349837, 371285319589761592, 371285319463546618, 371285319482586943, 371285319955003842, 371285319956415849, 371285319782567741, 371285319502447974]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 42810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 42800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362506227509515045, 362506253684483511⟩, ⟨(-897295398552805446), (-896537911318509820)⟩, true⟩

def words02 : List Nat := [371285319486452316, 371285319559372355, 371285319742655269, 371285319926506986, 371285320005973778, 371285320007415763, 371285320083601683, 371285320372989617, 371285321207856864, 371285321698041016]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 42820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 42800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500623089574347, 362500649277457193⟩, ⟨(-657228163941110360), (-656470123521963346)⟩, true⟩

def words03 : List Nat := [371285322187489292, 371285322677399453, 371285323288002379, 371285323714951121, 371285324256591798, 371285324798729830, 371285325338184702, 371285325339597096, 371285325509922817, 371285325869424655]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 42830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 42800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477636864248846, 362477663064706209⟩, ⟨327704080746392983, 328462659922851437⟩, true⟩

def words04 : List Nat := [371285326774066283, 371285327070367951, 371285327363533225, 371285327657148455, 371285327894869595, 371285327896426514, 371285328090491650, 371285328300636186, 371285328469541507, 371285328471005459]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 42840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 42800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362524884650526862, 362524910863727852⟩, ⟨(-1697079807214866243), (-1696320681907018853)⟩, true⟩

def words05 : List Nat := [371285328586156412, 371285328880894014, 371285329720552507, 371285330109628690, 371285330419844365, 371285330730507788, 371285331380868527, 371285331760378618, 371285332684788450, 371285333609769545]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 42850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 42800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362504176782585254, 362504203008550308⟩, ⟨(-809493646909248997), (-808733974468810153)⟩, true⟩

def words06 : List Nat := [371285334430253364, 371285334667922174, 371285335450578466, 371285336233952125, 371285337178029980, 371285337396722063, 371285337510199370, 371285337624144516, 371285338206974679, 371285338648622413]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 42860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 42800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507338713008416, 362507364951716278⟩, ⟨(-944977212691812018), (-944216993903316682)⟩, true⟩

def words07 : List Nat := [371285339532262055, 371285340416448918, 371285341314811449, 371285341835076045, 371285342381793377, 371285342929165702, 371285343932154750, 371285344449647664, 371285344964242552, 371285345479364810]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 42870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 42800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362502044797216612, 362502071048586598⟩, ⟨(-717807340971635656), (-717046579165176714)⟩, true⟩

def words08 : List Nat := [371285346476937064, 371285347277962719, 371285348330619663, 371285349383786629, 371285350343043795, 371285350674808841, 371285351358353531, 371285352042605470, 371285352777615600, 371285353168864392]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 42880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 42800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362503250098127715, 362503276362376917⟩, ⟨(-769510734381943093), (-768749420122302267)⟩, true⟩

def words09 : List Nat := [371285353457027787, 371285353745638095, 371285354472040385, 371285354928344376, 371285355450045383, 371285355972306615, 371285356500404117, 371285356501818744, 371285356793717705, 371285357213170085]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 42890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 42800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 42800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk428
