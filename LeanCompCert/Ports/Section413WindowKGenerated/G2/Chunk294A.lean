import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk294A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360604642516659828, 360604647706318786⟩, ⟨(-627639095371235363), (-627535907477049737)⟩, true⟩

def state01 : KState := ⟨⟨360609610421461931, 360609615614783862⟩, ⟨(-773762033939057858), (-773658738334882594)⟩, true⟩

def words00 : List Nat := [360583305553731958, 360583306690163923, 360583306952324789, 360583307214504465, 360583307214830270, 360583307966082926, 360583308716017169, 360583309465969390, 360583309638918117, 360583310533748370]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 29400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 29400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360683003412591054, 360683008609588136⟩, ⟨(-2932483916613938774), (-2932380512905561748)⟩, true⟩

def words01 : List Nat := [360583312581460154, 360583314629151458, 360583317467301526, 360583320955209966, 360583323357153507, 360583325758964026, 360583328683539641, 360583332191828082, 360583335580194452, 360583338968416675]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 29410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 29400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360650682527810181, 360650687728523201⟩, ⟨(-1981733251736267893), (-1981629738686688175)⟩, true⟩

def words02 : List Nat := [360583341491031927, 360583343283272173, 360583346227355949, 360583349171353466, 360583351333221107, 360583352347098192, 360583352535448843, 360583352723834974, 360583354063831369, 360583356352128017]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 29420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 29400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585408700387034, 360585413904767305⟩, ⟨(-60350407784589332), (-60246786788991970)⟩, true⟩

def words03 : List Nat := [360583359135387526, 360583361918533507, 360583364125772860, 360583365185467193, 360583365323264646, 360583365461152588, 360583366749937933, 360583367408317392, 360583367478181887, 360583367548095012]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 29430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 29400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360626198542925207, 360626203750990646⟩, ⟨(-1261234437560077815), (-1261130708055174601)⟩, true⟩

def words04 : List Nat := [360583368370590257, 360583370081445537, 360583372942619243, 360583375803674119, 360583377669458174, 360583378388534983, 360583379274507368, 360583380160535374, 360583380976118625, 360583382430558227]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 29440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 29400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk294A
