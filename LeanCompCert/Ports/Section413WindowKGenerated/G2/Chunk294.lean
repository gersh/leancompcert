import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk294

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

def state06 : KState := ⟨⟨360665055231983759, 360665060443759616⟩, ⟨(-2405845455038695041), (-2405741616243376345)⟩, true⟩

def words05 : List Nat := [360583383310104958, 360583384189634703, 360583386218707461, 360583388830192627, 360583390886874057, 360583392943485941, 360583394422543099, 360583396380531889, 360583399152879385, 360583401925167465]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 29450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 29400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360635933508292669, 360635938723746993⟩, ⟨(-1547958394234383455), (-1547854447053190763)⟩, true⟩

def words06 : List Nat := [360583405083544070, 360583407096244582, 360583408139563057, 360583409182847156, 360583409725055350, 360583410836552972, 360583412768322502, 360583414700035529, 360583415667786499, 360583417450391723]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 29460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 29400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360658104117278372, 360658109336414424⟩, ⟨(-2201511076790697613), (-2201407021090532135)⟩, true⟩

def words07 : List Nat := [360583419563839897, 360583421677257225, 360583424938341007, 360583427054405344, 360583428158254761, 360583429262056071, 360583430337025699, 360583432208886673, 360583434742348046, 360583437275728202]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 29470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 29400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360646660313439541, 360646665536291820⟩, ⟨(-1864372541921457545), (-1864268376648784271)⟩, true⟩

def words08 : List Nat := [360583439160623451, 360583439901025560, 360583441788438447, 360583443675851157, 360583445275293609, 360583446367845462, 360583446887458463, 360583447407079640, 360583448568174916, 360583450712221806]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 29480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 29400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360553532169411417, 360553537395945828⟩, ⟨882319781383298801, 882424055260492741⟩, true⟩

def words09 : List Nat := [360583452239102860, 360583453765947516, 360583454599721190, 360583454600111757, 360583454290224596, 360583453260021603, 360583452229775878, 360583451531173745, 360583451089403961, 360583450075785167]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 29490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 29400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 29400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk294
