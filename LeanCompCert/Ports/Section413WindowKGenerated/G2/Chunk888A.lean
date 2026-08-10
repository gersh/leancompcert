import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk888A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360556790605867347, 360556842384351272⟩, ⟨2237880113190218313, 2240985056797193197⟩, true⟩

def state01 : KState := ⟨⟨360570202630340196, 360570254420898766⟩, ⟨1046832631130256926, 1049938647024835148⟩, true⟩

def words00 : List Nat := [360582078419403613, 360582078263106033, 360582078109762703, 360582077842901814, 360582077575838039, 360582077277306358, 360582077067961384, 360582076985436570, 360582076902790448, 360582076722970885]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 88800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 88800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360610810282065742, 360610862084704462⟩, ⟨(-2559756633019781178), (-2556649544226731588)⟩, true⟩

def words01 : List Nat := [360582076590888163, 360582076585757666, 360582076700240659, 360582076808398248, 360582076811376220, 360582076814481496, 360582076943859364, 360582077142812804, 360582077467929487, 360582077793329374]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 88810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 88800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586448659985028, 360586500474852236⟩, ⟨(-395936053748483867), (-392827878764701327)⟩, true⟩

def words02 : List Nat := [360582078042894026, 360582078198070656, 360582078350128390, 360582078502540826, 360582078533768597, 360582078535050840, 360582078508125983, 360582078403282986, 360582078298201586, 360582078281262558]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 88820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 88800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360559090946939080, 360559142773848373⟩, ⟨2034449484919878052, 2037558729664179598⟩, true⟩

def words03 : List Nat := [360582078436379019, 360582078591737435, 360582078683506502, 360582078684787024, 360582078649916034, 360582078569323510, 360582078488366013, 360582078374742298, 360582078180729248, 360582077923889618]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 88830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 88800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577997000637605, 360578048839639954⟩, ⟨354798494199243188, 357908813348598388⟩, true⟩

def words04 : List Nat := [360582077666765372, 360582077504536448, 360582077511146489, 360582077578473873, 360582077579655050, 360582077539519496, 360582077424899190, 360582077288831598, 360582077152379077, 360582077076143597]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 88840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 88800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk888A
