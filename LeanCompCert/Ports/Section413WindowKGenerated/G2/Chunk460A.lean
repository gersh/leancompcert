import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk460A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk460A
