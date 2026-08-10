import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk167A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360716766373484057, 360716767965924424⟩, ⟨(-2237278234224434821), (-2237260230988526177)⟩, true⟩

def state01 : KState := ⟨⟨360635543518366264, 360635545112815920⟩, ⟨(-880466313285980526), (-880448276484711530)⟩, true⟩

def words00 : List Nat := [360582814173680580, 360582820168544510, 360582829736761201, 360582839303895990, 360582846840228951, 360582850827021947, 360582853010587848, 360582855193915428, 360582855209734207, 360582858362981398]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 16700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 16700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360566526443597325, 360566528040033362⟩, ⟨273223296776442194, 273241366780163382⟩, true⟩

def words01 : List Nat := [360582862649906378, 360582866936358169, 360582869406354630, 360582869758605986, 360582869758782593, 360582869172908278, 360582870383276466, 360582871204095632, 360582871204283594, 360582870227041745]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 16710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 16700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360647724959630684, 360647726558059490⟩, ⟨(-1085093621247886792), (-1085075517915031976)⟩, true⟩

def words02 : List Nat := [360582869853792770, 360582872299165220, 360582874644788497, 360582876990168773, 360582876990363467, 360582876118411876, 360582871706573174, 360582869446436520, 360582868487430089, 360582872364172990]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 16720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 16700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360561749936244192, 360561751536684162⟩, ⟨353762376241120166, 353780513230669130⟩, true⟩

def words03 : List Nat := [360582873291824400, 360582874219384293, 360582876944941783, 360582881450353032, 360582885024365812, 360582888597985935, 360582889387240754, 360582889387451986, 360582886640881781, 360582885378573689]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 16730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 16700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360628058463641623, 360628060066070805⟩, ⟨(-756555465384892106), (-756537295085918552)⟩, true⟩

def words04 : List Nat := [360582886409278342, 360582888218370439, 360582888235699183, 360582888253053821, 360582888253231186, 360582886145194063, 360582889032581811, 360582892252575125, 360582893660175129, 360582896356734890]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 16740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 16700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk167A
