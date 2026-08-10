import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk353A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360657718695116936, 360657726292617446⟩, ⟨(-2674828966256110423), (-2674647653412643915)⟩, true⟩

def state01 : KState := ⟨⟨360613476307426962, 360613483909445296⟩, ⟨(-1113026236194355807), (-1112844763850024543)⟩, true⟩

def words00 : List Nat := [360581960838738357, 360581961960421065, 360581963575055366, 360581965189736692, 360581966359750782, 360581966965992991, 360581967172096005, 360581967378245615, 360581967489648023, 360581968382729825]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 35300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 35300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360560320040709730, 360560327647181811⟩, ⟨764333803381255778, 764515433010357898⟩, true⟩

def words01 : List Nat := [360581970076383792, 360581971770032521, 360581972988266210, 360581973407740356, 360581973408143775, 360581973269748607, 360581973792933419, 360581973793407365, 360581973656856128, 360581973044492411]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 35310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 35300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594341272686890, 360594348883639700⟩, ⟨(-437469662446394168), (-437287874535879870)⟩, true⟩

def words02 : List Nat := [360581972432061408, 360581971373546925, 360581971408448833, 360581971826384138, 360581971826825597, 360581971540844259, 360581971246324046, 360581971499543113, 360581971643564254, 360581971994377130]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 35320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 35300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590644433525884, 360590652048992121⟩, ⟨(-306839507730902149), (-306657560339150799)⟩, true⟩

def words03 : List Nat := [360581971994799390, 360581971940665282, 360581972414216247, 360581973464789471, 360581974113381138, 360581974762021418, 360581975005930698, 360581975006404848, 360581974698129410, 360581974944203373]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 35330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 35300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590198769743941, 360590206389681686⟩, ⟨(-291204661133023100), (-291022555696358322)⟩, true⟩

def words04 : List Nat := [360581975702174988, 360581976018861574, 360581976019299626, 360581975513938573, 360581975008528646, 360581974302568145, 360581974127831521, 360581974158555051, 360581974158977500, 360581974018441938]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 35340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 35300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk353A
