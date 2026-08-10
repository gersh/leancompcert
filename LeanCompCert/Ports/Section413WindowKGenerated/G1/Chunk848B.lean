import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk848A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk848B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk848A

def state06 : KState := ⟨⟨362501381664388124, 362501490138644407⟩, ⟨(-1378668918538522010), (-1372453463928819994)⟩, true⟩

def words05 : List Nat := [371285316712480212, 371285316649108216, 371285316636938284, 371285316644887050, 371285316647167911, 371285316632750153, 371285316738240114, 371285316793303893, 371285316985891426, 371285317179759539]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489915135801940, 362490023636733754⟩, ⟨(-405613643274253738), (-399395924852614562)⟩, true⟩

def words06 : List Nat := [371285317347164402, 371285317350112354, 371285317471649374, 371285317599901829, 371285317731904734, 371285317734852699, 371285317681929328, 371285317629982507, 371285317660375870, 371285317719225388]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481111501718806, 362481220029198628⟩, ⟨341642672645514553, 347862644334163673⟩, true⟩

def words07 : List Nat := [371285317915410247, 371285318112817214, 371285318304159029, 371285318311223920, 371285318313332690, 371285318314825505, 371285318404900360, 371285318407852449, 371285318361645914, 371285318316714347]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480787706829174, 362480896260734799⟩, ⟨369179078015561237, 375401292860553115⟩, true⟩

def words08 : List Nat := [371285318309810480, 371285318313118632, 371285318419411600, 371285318527061182, 371285318611321441, 371285318614270072, 371285318513304954, 371285318485362859, 371285318466324137, 371285318469391420]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489844147095883, 362489952727835082⟩, ⟨(-399677967447057997), (-393453474562554983)⟩, true⟩

def words09 : List Nat := [371285318419502773, 371285318370531525, 371285318367798946, 371285318371048787, 371285318371871390, 371285318395762551, 371285318418762667, 371285318421740004, 371285318407666608, 371285318465876300]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk848B
