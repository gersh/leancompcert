import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk241A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582493640279289, 360582497067694110⟩, ⟨(-331138799538716), (-275257276225312)⟩, true⟩

def state01 : KState := ⟨⟨360674960979627894, 360674964410012082⟩, ⟨(-2229465673466621053), (-2229409720367045973)⟩, true⟩

def words00 : List Nat := [360582485646964482, 360582484982077128, 360582486945551790, 360582488908923858, 360582489415835658, 360582489416150582, 360582491062867123, 360582492746682384, 360582496150858121, 360582499986289838]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 24100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 24100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360658208756899998, 360658212190277394⟩, ⟨(-1825495033944192563), (-1825439008663650659)⟩, true⟩

def words01 : List Nat := [360582502695690181, 360582505404898587, 360582509833990081, 360582515121629025, 360582518894704073, 360582522667511571, 360582525572072523, 360582527500882595, 360582530638976524, 360582533776917101]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 24110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 24100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360677961710639377, 360677965146982789⟩, ⟨(-2301984072164913739), (-2301927975329241283)⟩, true⟩

def words02 : List Nat := [360582538633320114, 360582543534932279, 360582546788790591, 360582550042410873, 360582552792054694, 360582556398274787, 360582560782689045, 360582565166801184, 360582568214401126, 360582572168020905]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 24120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 24100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360797235855109399, 360797239294420197⟩, ⟨(-5180748257790371920), (-5180692089336879306)⟩, true⟩

def words03 : List Nat := [360582577212729326, 360582582257111346, 360582589017880373, 360582595525241134, 360582600580383060, 360582605635136039, 360582612405963691, 360582620126129810, 360582629016987934, 360582637907181190]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 24130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 24100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360675829658474579, 360675833100786085⟩, ⟨(-2249730271308186680), (-2249674030403045188)⟩, true⟩

def words04 : List Nat := [360582645715045515, 360582651820378669, 360582657862301122, 360582663903810497, 360582668820767672, 360582672035729420, 360582674383271225, 360582676730650275, 360582678896263129, 360582682753785835]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 24140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 24100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk241A
