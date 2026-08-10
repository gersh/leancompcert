import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk275A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk275A
