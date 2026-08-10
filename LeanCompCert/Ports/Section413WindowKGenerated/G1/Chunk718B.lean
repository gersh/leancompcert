import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk718A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk718B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk718A

def state06 : KState := ⟨⟨362481741064507230, 362481817856816984⟩, ⟨243071607937871237, 246798349736640303⟩, true⟩

def words05 : List Nat := [371285251982681041, 371285252170152282, 371285252344821543, 371285252347287590, 371285252298388249, 371285252258499170, 371285252351277623, 371285252353750217, 371285252334786607, 371285252289738452]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487063045683782, 362487139860069043⟩, ⟨(-139328405184563871), (-135600076926630569)⟩, true⟩

def words06 : List Nat := [371285252389247643, 371285252480813630, 371285252645648783, 371285252811505324, 371285252946381050, 371285252948846483, 371285252893970285, 371285252965319011, 371285253116499349, 371285253145303330]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490515967299130, 362490592804190879⟩, ⟨(-387494944120994377), (-383764998209568745)⟩, true⟩

def words07 : List Nat := [371285253173794986, 371285253203153719, 371285253380274776, 371285253489999089, 371285253623603777, 371285253758175877, 371285253874052547, 371285253876518702, 371285253833414860, 371285253910766893]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488088187137039, 362488165046013022⟩, ⟨(-212979265743930904), (-209247739490382022)⟩, true⟩

def words08 : List Nat := [371285254180034756, 371285254216060070, 371285254217954014, 371285254207924785, 371285254196985411, 371285254195258431, 371285254187530098, 371285254282189861, 371285254377948845, 371285254421046192]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497766966310454, 362497843847440645⟩, ⟨(-908860618909258345), (-905127492688314265)⟩, true⟩

def words09 : List Nat := [371285254550609595, 371285254681445697, 371285254933887843, 371285254949861299, 371285254951770139, 371285254936729438, 371285254983888477, 371285254986610587, 371285255145208437, 371285255323043373]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk718B
