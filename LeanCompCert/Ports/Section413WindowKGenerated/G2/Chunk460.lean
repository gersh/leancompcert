import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk460

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360552277698776735, 360552290882717484⟩, ⟨1423116039313492172, 1423525860027907712⟩, true⟩

def state01 : KState := ⟨⟨360600569092383339, 360600582282279779⟩, ⟨(-798470673003298657), (-798060578298462119)⟩, true⟩

def words00 : List Nat := [360583236424846892, 360583236288025404, 360583236822016846, 360583237356117369, 360583237488084594, 360583237488715561, 360583237149307644, 360583236948461739, 360583236909353024, 360583237286989556]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589622808035011, 360589636003948381⟩, ⟨(-294872294975983502), (-294461923402732562)⟩, true⟩

def words01 : List Nat := [360583237298968043, 360583237311005073, 360583237311518966, 360583237410327718, 360583237458934066, 360583237507641248, 360583237508208644, 360583237319215883, 360583237439048861, 360583237578807625]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582495714787797, 360582508916638851⟩, ⟨33114560954019060, 33525205809888454⟩, true⟩

def words02 : List Nat := [360583238189360017, 360583238328956727, 360583238329520234, 360583238120418428, 360583237911228328, 360583237366407614, 360583237222129169, 360583237385820919, 360583237386383272, 360583237250460487]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360584080271195747, 360584093479013796⟩, ⟨(-39821462927589646), (-39410543381695280)⟩, true⟩

def words03 : List Nat := [360583237588869393, 360583237943282534, 360583238435956193, 360583238457915616, 360583238458507930, 360583238043860501, 360583237629109671, 360583237452658440, 360583237471770844, 360583237491016540]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360605425777298467, 360605438991127520⟩, ⟨(-1022944464747552848), (-1022533268425994952)⟩, true⟩

def words04 : List Nat := [360583237491578993, 360583237226759745, 360583236491173429, 360583236035862746, 360583235580398377, 360583235005883059, 360583234849250892, 360583234456945525, 360583234142015351, 360583234624915582]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360536696121982715, 360536709341767932⟩, ⟨2142551135873338208, 2142962606505098452⟩, true⟩

def words05 : List Nat := [360583235577946187, 360583236531056887, 360583237042474225, 360583237083497157, 360583237084025814, 360583236921522370, 360583236758843066, 360583236519375951, 360583235809469267, 360583234800007296]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 46050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 46000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575355504067988, 360575368729812326⟩, ⟨361766196888844222, 362177942027225438⟩, true⟩

def words06 : List Nat := [360583233790434516, 360583233251324511, 360583233004673512, 360583233054514728, 360583233055097555, 360583232668003596, 360583232005273937, 360583231331556790, 360583230657679921, 360583230200227504]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 46060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 46000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552753904022869, 360552767135788322⟩, ⟨1403257360809287772, 1403669383371288014⟩, true⟩

def words07 : List Nat := [360583230030157460, 360583229623289116, 360583229278779083, 360583229700392489, 360583229853204775, 360583230006111737, 360583230006674650, 360583229924059024, 360583229371294001, 360583228710948290]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 46070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 46000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360521695104862160, 360521708342586288⟩, ⟨2834430505358076520, 2834842802526250344⟩, true⟩

def words08 : List Nat := [360583228050424485, 360583227217255885, 360583225914059531, 360583224375569152, 360583222837044749, 360583221038906146, 360583219477242207, 360583218074395040, 360583216671534621, 360583215020879329]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 46080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 46000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583388570264129, 360583401813951430⟩, ⟨(-9362065961099651), (-8949493920872469)⟩, true⟩

def words09 : List Nat := [360583213686928692, 360583212822809224, 360583211958541094, 360583211563999603, 360583210972066893, 360583209935260698, 360583208898378545, 360583208141627586, 360583207681107066, 360583207685973277]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 46090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 46000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 46000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk460
