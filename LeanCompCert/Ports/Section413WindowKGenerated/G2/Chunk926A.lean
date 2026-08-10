import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk926A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360597108379595557, 360597164868093843⟩, ⟨(-1407863668447805923), (-1404331458733571685)⟩, true⟩

def state01 : KState := ⟨⟨360579697268801524, 360579753770079975⟩, ⟨204394788667274989, 207928181885914117⟩, true⟩

def words00 : List Nat := [360581999572375346, 360581999573714900, 360581999564301458, 360581999552632552, 360581999540608593, 360581999499648731, 360581999407210138, 360581999256377596, 360581999105298885, 360581998972346317]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 92600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 92600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360546733289687974, 360546789803574095⟩, ⟨3257421665276680532, 3260956226155645642⟩, true⟩

def words01 : List Nat := [360581998992899198, 360581999037957222, 360581999039150683, 360581999025677815, 360581998895691012, 360581998736934712, 360581998577803333, 360581998391120722, 360581998088017068, 360581997709276489]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 92610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 92600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579458988725242, 360579515515250994⟩, ⟨226186782171169812, 229722513793934016⟩, true⟩

def words02 : List Nat := [360581997330232248, 360581997006797370, 360581996753643008, 360581996617209991, 360581996480662463, 360581996248679083, 360581995953827680, 360581995775819496, 360581995597406473, 360581995516479473]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 92620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 92600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582612018222969, 360582668557524388⟩, ⟨(-65967067496651537), (-62430152399718459)⟩, true⟩

def words03 : List Nat := [360581995490929303, 360581995356045705, 360581995220911122, 360581995125666190, 360581995088260980, 360581995000442395, 360581994912492346, 360581994756153108, 360581994655386766, 360581994664189907]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 92630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 92600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595343634906088, 360595400186821882⟩, ⟨(-1245496164547147998), (-1241958080791163760)⟩, true⟩

def words04 : List Nat := [360581994788940855, 360581994895958633, 360581994944348557, 360581994992888921, 360581994994029914, 360581994987518816, 360581995130376432, 360581995273488637, 360581995349154917, 360581995495228795]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 92640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 92600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk926A
