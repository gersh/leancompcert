import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk375

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360545475147067500, 360545483763691351⟩, ⟨1351325836773716856, 1351544257878328450⟩, true⟩

def state01 : KState := ⟨⟨360588819950084223, 360588828571468932⟩, ⟨(-274383419563463978), (-274164819903507118)⟩, true⟩

def words00 : List Nat := [360581523983237687, 360581523733108659, 360581523249371474, 360581522410363765, 360581521571320303, 360581520331412945, 360581519718298965, 360581519767170912, 360581519767621244, 360581519653554094]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360609261225723194, 360609269851884971⟩, ⟨(-1041325282432470384), (-1041106503561337726)⟩, true⟩

def words01 : List Nat := [360581520558888359, 360581521464327578, 360581522115211146, 360581522115716864, 360581522058394405, 360581521323363477, 360581520588274857, 360581521070229595, 360581521810212743, 360581522550278902]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591193549363583, 360591202180342414⟩, ⟨(-363599623611149441), (-363380663980716661)⟩, true⟩

def words02 : List Nat := [360581522737457078, 360581522737962994, 360581522673309291, 360581522907875799, 360581522908300544, 360581522761396257, 360581522243765372, 360581521184390035, 360581520124974326, 360581520033211224]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360566550988344481, 360566559624086105⟩, ⟨561451452798991473, 561670591201281865⟩, true⟩

def words03 : List Nat := [360581520501705935, 360581520970274022, 360581521081560660, 360581521236170080, 360581521236593519, 360581521209125478, 360581521862562955, 360581521944724911, 360581521945179996, 360581521547133556]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588045025821449, 360588053666346494⟩, ⟨(-245691563403171240), (-245472245407497800)⟩, true⟩

def words04 : List Nat := [360581521149001268, 360581520564618964, 360581520336196540, 360581520210519897, 360581520084806996, 360581519357492471, 360581517923233610, 360581517197974153, 360581516472590374, 360581516630171493]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360545785198081518, 360545793843424699⟩, ⟨1341411393750554061, 1341630892690418367⟩, true⟩

def words05 : List Nat := [360581516630622372, 360581516448394495, 360581516266080697, 360581516630208301, 360581516630639879, 360581516439075122, 360581516247471785, 360581515603105153, 360581514466205309, 360581513515754050]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580276005979806, 360580284656098168⟩, ⟨45754909673589643, 45974587993281263⟩, true⟩

def words06 : List Nat := [360581512565185795, 360581512323026845, 360581512104313540, 360581511462783234, 360581510821207361, 360581509725157072, 360581508987840106, 360581508958779500, 360581508929672937, 360581508360862429]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360641880443947886, 360641889098842112⟩, ⟨(-2269081344563986216), (-2268861486791302920)⟩, true⟩

def words07 : List Nat := [360581509004164661, 360581509680150090, 360581511063945055, 360581511741943177, 360581511807641119, 360581511873382544, 360581512417142917, 360581513316573195, 360581514923576253, 360581516530608396]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360611642690710045, 360611651350437162⟩, ⟨(-1132816958633763536), (-1132596919217888486)⟩, true⟩

def words08 : List Nat := [360581517781028968, 360581519159288453, 360581520158054204, 360581521156912071, 360581521973762722, 360581522085197189, 360581522085652779, 360581521514153783, 360581521077989711, 360581521880106022]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360558606338877589, 360558615003373134⟩, ⟨861228528046598172, 861448746731664448⟩, true⟩

def words09 : List Nat := [360581523389310697, 360581524898532379, 360581526054777462, 360581526505822748, 360581526650575551, 360581526795457263, 360581526795874379, 360581526692363984, 360581526483119374, 360581525874296849]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk375
