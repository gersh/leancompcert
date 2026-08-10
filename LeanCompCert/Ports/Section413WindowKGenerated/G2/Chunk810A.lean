import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk810A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580509807245429, 360580552583191665⟩, ⟨128802643377197460, 131142694205383144⟩, true⟩

def state01 : KState := ⟨⟨360580911109023610, 360580953895885844⟩, ⟨96283256457619605, 98624191536469793⟩, true⟩

def words00 : List Nat := [360582171741976857, 360582171764347316, 360582171765386143, 360582171677636770, 360582171589674967, 360582171411355143, 360582171355758587, 360582171379764210, 360582171380806993, 360582171328197121]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 81000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 81000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360599784136095464, 360599826933919827⟩, ⟨(-1432819029807234996), (-1430477206632431334)⟩, true⟩

def words01 : List Nat := [360582171314123028, 360582171260330505, 360582171303304835, 360582171304464401, 360582171250645798, 360582171048112328, 360582170845353212, 360582170860901748, 360582171079761656, 360582171298879129]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 81010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 81000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599456177837650, 360599498986702868⟩, ⟨(-1406302592770796102), (-1403959875012741780)⟩, true⟩

def words02 : List Nat := [360582171436032469, 360582171522056070, 360582171760001261, 360582171998281104, 360582172132364306, 360582172303037332, 360582172397397093, 360582172491870694, 360582172564608697, 360582172779757221]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 81020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 81000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567049432597854, 360567092252397783⟩, ⟨1219892359696611230, 1222235963549936666⟩, true⟩

def words03 : List Nat := [360582173146640213, 360582173513756613, 360582173804597212, 360582174004120814, 360582174129438320, 360582174255070192, 360582174364024836, 360582174365184838, 360582174322342236, 360582174137436652]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 81030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 81000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360617362277379454, 360617405108125854⟩, ⟨(-2857705813730905893), (-2855361322720360273)⟩, true⟩

def words04 : List Nat := [360582173952272593, 360582173981330926, 360582174196134625, 360582174411155318, 360582174497373928, 360582174590867129, 360582174836193676, 360582175081863466, 360582175479252650, 360582175915115030]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 81040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 81000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk810A
