import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk030

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360219058782059532, 360219058825033369⟩, ⟨1100287598942182366, 1100287686532179862⟩, true⟩

def state01 : KState := ⟨⟨360364845071955287, 360364845115231255⟩, ⟨661901954405476053, 661902042903392573⟩, true⟩

def words00 : List Nat := [360585699173787079, 360585686721657085, 360585643832424933, 360585496360707332, 360585348987135445, 360585170249759538, 360585051136710430, 360584977671135948, 360584904254388608, 360584746126162615]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 3000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 3000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360969606356371208, 360969606399950694⟩, ⟨(-1161698778060387121), (-1161698688647329225)⟩, true⟩

def words01 : List Nat := [360584709014376231, 360584744911306188, 360584818880114138, 360584887370515021, 360584887370544882, 360584857696973139, 360584828043066500, 360584810544095519, 360584937959967949, 360585065291494114]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 3010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 3000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360685943909514310, 360685943953401242⟩, ⟨(-306154359621510891), (-306154269278431691)⟩, true⟩

def words02 : List Nat := [360585122081246173, 360585122081278464, 360585130405059388, 360585188597667508, 360585188597694754, 360585176472223999, 360585143881978960, 360585055345015180, 360584966866504954, 360584936276305092]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 3020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 3000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360541679344745972, 360541679388938300⟩, ⟨130989658386045433, 130989749656013703⟩, true⟩

def words03 : List Nat := [360584963066980896, 360584989839996321, 360584989840025409, 360584959109329569, 360584900612735698, 360584811724908426, 360584741065968556, 360584782300904777, 360584782300933668, 360584768122377779]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 3030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 3000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360997734372161096, 360997734416660465⟩, ⟨(-1257255666143080741), (-1257255573938172419)⟩, true⟩

def words04 : List Nat := [360584846471153334, 360585006829140300, 360585194583934619, 360585382215414986, 360585465786660056, 360585465786692656, 360585444354975405, 360585434047514361, 360585519474351916, 360585654582527993]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 3040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 3000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360572683351294841, 360572683396106082⟩, ⟨42167126678835668, 42167219836489288⟩, true⟩

def words05 : List Nat := [360585735329804969, 360585816024188765, 360585943129901784, 360586124580223365, 360586239460853412, 360586354266329607, 360586414621956783, 360586468038027836, 360586468038054940, 360586463533307550]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 3050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 3000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360746615771752496, 360746615816872819⟩, ⟨(-491321135235473444), (-491321041130446096)⟩, true⟩

def words06 : List Nat := [360586559783390135, 360586559783422938, 360586556706684019, 360586499584665424, 360586442499915295, 360586355883246330, 360586453881664361, 360586555215522139, 360586576389760532, 360586628502926077]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 3060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 3000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361068963232817153, 361068963278248695⟩, ⟨(-1484160566157103512), (-1484160471095089112)⟩, true⟩

def words07 : List Nat := [360586726055185052, 360586823543963554, 360586915076631227, 360586973010842346, 360586973010872686, 360586933858065168, 360586894730700199, 360586936493161112, 360587092995390790, 360587249396036722]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 3070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 3000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361036890470065706, 361036890515811340⟩, ⟨(-1387578665813240036), (-1387578569782225520)⟩, true⟩

def words08 : List Nat := [360587335940158932, 360587394176956998, 360587556084360985, 360587717886810174, 360587850893921508, 360587881805454003, 360587881805484201, 360587832053154745, 360587835962446244, 360587981240566363]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 3080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 3000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360664178974084256, 360664179020142109⟩, ⟨(-232624909576312489), (-232624812578955625)⟩, true⟩

def words09 : List Nat := [360588137882950680, 360588294424052802, 360588398081196189, 360588570841782919, 360588715359049231, 360588859782997266, 360589037991959395, 360589114543608659, 360589138757985478, 360589162956749992]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 3090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 3000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 3000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk030
