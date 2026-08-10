import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk304A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk304B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk304A

def state06 : KState := ⟨⟨362452176509672233, 362452189382244834⟩, ⟨1017338842939131061, 1017603877427870171⟩, true⟩
def words05 : List Nat := [371285596269597587, 371285597518526554, 371285598769609470, 371285598770586990, 371285598730679695, 371285598875747088, 371285599260271658, 371285599261249380, 371285598353132880, 371285597257406616]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 30450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 30400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494909800478610, 362494922681800239⟩, ⟨(-284507621481221071), (-284242320452289617)⟩, true⟩
def words06 : List Nat := [371285596161328168, 371285596018631345, 371285595468427930, 371285595602387462, 371285595603151523, 371285595586809093, 371285594136655125, 371285593761705131, 371285594084770423, 371285594391936031]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 30460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 30400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499832995653538, 362499845885905942⟩, ⟨(-434549365583154199), (-434283792388571255)⟩, true⟩
def words07 : List Nat := [371285594476294209, 371285594560977018, 371285595532786384, 371285595973913447, 371285596512951500, 371285597052319240, 371285597594296365, 371285597595291793, 371285597728764160, 371285598197431530]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 30470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 30400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362451674697405166, 362451687596359400⟩, ⟨1033516686541775340, 1033782525014214976⟩, true⟩
def words08 : List Nat := [371285598862743587, 371285598863721974, 371285598097025453, 371285597344135452, 371285596590945444, 371285595817735596, 371285594504906418, 371285594076312021, 371285593647407309, 371285593221974822]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 30480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 30400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362512181981663106, 362512194889478821⟩, ⟨(-811588284896732800), (-811322176194728774)⟩, true⟩
def words09 : List Nat := [371285592110651515, 371285592072739533, 371285593067926519, 371285593068905378, 371285592829787591, 371285592484103328, 371285592863845998, 371285593288439012, 371285594161299151, 371285595034516862]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 30490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 30400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 30400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk304B
