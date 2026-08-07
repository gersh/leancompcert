import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk275

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360658236600488336, 360658241115040958⟩, ⟨(-2072317687751940495), (-2072233714323550503)⟩, true⟩

def state01 : KState := ⟨⟨360629271175124511, 360629275693127762⟩, ⟨(-1276086450688773738), (-1276002382351112168)⟩, true⟩

def words00 : List Nat := [360582891861360067, 360582892503972253, 360582893113158592, 360582893722405050, 360582893994583247, 360582893994946306, 360582893859160624, 360582892958079999, 360582892472702684, 360582894159110420]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 27500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 27500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360499273198927474, 360499277720337295⟩, ⟨2300875056124860284, 2300959218195046256⟩, true⟩

def words01 : List Nat := [360582895455250536, 360582896751364337, 360582897375858359, 360582897376220610, 360582896685080265, 360582895657676896, 360582894630247412, 360582893570267994, 360582891194950320, 360582888157044964]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 27510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 27500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360547733077703119, 360547737602533093⟩, ⟨966875229333399216, 966959485543222184⟩, true⟩

def words02 : List Nat := [360582885119280173, 360582881878469186, 360582879647187399, 360582877861719991, 360582876076348152, 360582873150027222, 360582868909046568, 360582865983720686, 360582863058500995, 360582861448720642]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 27520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 27500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360552359038927190, 360552363567217490⟩, ⟨839307482393719819, 839391833882743795⟩, true⟩

def words03 : List Nat := [360582860173260588, 360582857797013417, 360582855420871578, 360582853240617995, 360582851914567271, 360582850253576983, 360582848592667872, 360582846100700040, 360582843679870975, 360582842573531316]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 27530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 27500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360550064438220114, 360550068969922513⟩, ⟨902484205873280610, 902568651348772454⟩, true⟩

def words04 : List Nat := [360582841674643318, 360582841675005984, 360582841036078972, 360582839735259612, 360582838434478438, 360582836217306436, 360582834663285881, 360582833356518154, 360582832049808640, 360582830082494157]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 27540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 27500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360578563248685596, 360578567783817019⟩, ⟨117340529316784767, 117425069278768497⟩, true⟩

def words05 : List Nat := [360582829017891260, 360582829142500225, 360582830138539578, 360582830575004831, 360582830575341399, 360582829702462888, 360582828829579199, 360582828644176587, 360582828644475358, 360582828490249486]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 27550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 27500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575202941273384, 360575207479857128⟩, ⟨209631012139969164, 209715647265536052⟩, true⟩

def words06 : List Nat := [360582828335980913, 360582827520889862, 360582825394765937, 360582824080024383, 360582822765282604, 360582820756483126, 360582819464221507, 360582817504645845, 360582815545143651, 360582814140983916]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 27560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 27500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360481075694162199, 360481080236170683⟩, ⟨2805435594395848623, 2805520323958682193⟩, true⟩

def words07 : List Nat := [360582814512028650, 360582815158989441, 360582815159319997, 360582814686886858, 360582813805604340, 360582812585913389, 360582811366203574, 360582809799771322, 360582806923629170, 360582803235589055]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 27570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 27500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360568990116403134, 360568994661838185⟩, ⟨380420723079028145, 380505547163583393⟩, true⟩

def words08 : List Nat := [360582799547728053, 360582797170378525, 360582795454922084, 360582795049702675, 360582794644487334, 360582793109791316, 360582791206452335, 360582789219372148, 360582787232326504, 360582786091601273]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 27580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 27500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360516128286069876, 360516132834965397⟩, ⟨1839305384081988167, 1839390303657837013⟩, true⟩

def words09 : List Nat := [360582785592073367, 360582784149974588, 360582782707911071, 360582782382879584, 360582782399825515, 360582782416829462, 360582782417153269, 360582781775299099, 360582779825515842, 360582777411184884]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 27590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 27500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 27500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk275
