import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk036

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360536689620326491, 360536689683557438⟩, ⟨55569538795573031, 55569693443417555⟩, true⟩

def state01 : KState := ⟨⟨360390138367099781, 360390138430701025⟩, ⟨582296998461415143, 582297154444232753⟩, true⟩

def words00 : List Nat := [360552135997883535, 360552135997922836, 360552074960284354, 360551974818721781, 360551874732710373, 360551717692253932, 360551601044847184, 360551560268655040, 360551519515055614, 360551439581516602]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 3600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 3600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360741194779468964, 360741194843443084⟩, ⟨(-686253892489680040), (-686253735158920682)⟩, true⟩

def words01 : List Nat := [360551394912163173, 360551377848623980, 360551419306888697, 360551462614403575, 360551462614439913, 360551440327158074, 360551471248161595, 360551569605690799, 360551621988385949, 360551674342156445]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 3610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 3600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360673881053734257, 360673881118085423⟩, ⟨(-444779331946895589), (-444779173249386941)⟩, true⟩

def words02 : List Nat := [360551674342191805, 360551669824347455, 360551590593450998, 360551586719767836, 360551582848211723, 360551545737297103, 360551528386875982, 360551460860536557, 360551393371404624, 360551386165386611]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 3620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 3600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360647031533528365, 360647031598253911⟩, ⟨(-346397404398861446), (-346397244340429176)⟩, true⟩

def words03 : List Nat := [360551494876374129, 360551603527522712, 360551653608093600, 360551681082195830, 360551687951945802, 360551694817928740, 360551776451479641, 360551841368899117, 360551867520096478, 360551893656935474]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 3630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 3600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360780871452869222, 360780871517970229⟩, ⟨(-833819750156152999), (-833819588729130625)⟩, true⟩

def words04 : List Nat := [360551926526085344, 360551998530158652, 360552144992574780, 360552291374634936, 360552373739338549, 360552382458085158, 360552386810833297, 360552391161206664, 360552427794989521, 360552490365209580]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 3640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 3600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360738897523529669, 360738897589010982⟩, ⟨(-681015367302117998), (-681015204485109708)⟩, true⟩

def words05 : List Nat := [360552514601923788, 360552538825373088, 360552581789724810, 360552687885359337, 360552742077171881, 360552796239353463, 360552799973544476, 360552799973584492, 360552827860964212, 360552878685846517]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 3650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 3600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360368024381925865, 360368024447784996⟩, ⟨676689497642452976, 676689661844173216⟩, true⟩

def words06 : List Nat := [360552925445761631, 360552925445801655, 360552899216976942, 360552808944644399, 360552718721567316, 360552608389176035, 360552547749152442, 360552513925379687, 360552480120039593, 360552408551829730]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 3660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 3600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361109183437273926, 361109183503512158⟩, ⟨(-2046712329144714119), (-2046712163549791289)⟩, true⟩

def words07 : List Nat := [360552381351401256, 360552404365660768, 360552500554628086, 360552591762017268, 360552612907350557, 360552634041184959, 360552728231884075, 360552860545147555, 360553011719897263, 360553162812517920]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 3670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 3600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360800776329129497, 360800776395751781⟩, ⟨(-910806123566062020), (-910805956555928430)⟩, true⟩

def words08 : List Nat := [360553275902256684, 360553394625891889, 360553543954707596, 360553693202487953, 360553789463987400, 360553866650259825, 360553906355260951, 360553946038740295, 360553946038773682, 360554012386931427]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 3680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 3600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360535728261093931, 360535728328096673⟩, ⟨69665023602392008, 69665192018358666⟩, true⟩

def words09 : List Nat := [360554151736412180, 360554291010433876, 360554392956526317, 360554423350945152, 360554433924564395, 360554444492474982, 360554527308470474, 360554561848434337, 360554561848470738, 360554556758371906]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 3690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 3600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 3600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk036
