import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk332A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360658802101107166, 360658808787505867⟩, ⟨(-2575680518367246228), (-2575530421196829558)⟩, true⟩

def state01 : KState := ⟨⟨360626545226830355, 360626551917460997⟩, ⟨(-1504757288635111769), (-1504607050943862465)⟩, true⟩

def words00 : List Nat := [360581236451473219, 360581237745892532, 360581239945368231, 360581242144841183, 360581243899496510, 360581244750134933, 360581245145808737, 360581245541514681, 360581246073802345, 360581247438494876]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 33200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 33200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580032774781062, 360580039469586712⟩, ⟨40264245759190222, 40414622123593554⟩, true⟩

def words01 : List Nat := [360581249707745776, 360581251976946365, 360581253791420020, 360581254702175796, 360581254828611537, 360581254955148796, 360581255661294654, 360581256080367354, 360581256080766270, 360581256044605484]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 33210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 33200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360633848965205408, 360633855664201731⟩, ⟨(-1747590274999933278), (-1747439759400975330)⟩, true⟩

def words02 : List Nat := [360581256655967026, 360581257987435867, 360581260222695087, 360581262457904553, 360581263919563589, 360581264887622295, 360581266498184271, 360581268108785915, 360581269453709447, 360581271036613005]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 33220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 33200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360601554631337061, 360601561334557939⟩, ⟨(-674274658839143304), (-674124002837804814)⟩, true⟩

def words03 : List Nat := [360581271879786656, 360581272722954834, 360581274278004919, 360581276405471404, 360581277814261774, 360581279223045819, 360581280171674797, 360581280218050488, 360581280828551560, 360581281439162560]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 33230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 33200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360623932945270108, 360623939652678004⟩, ⟨(-1418395313960428312), (-1418244518761668500)⟩, true⟩

def words04 : List Nat := [360581282313354667, 360581283060131365, 360581283111013336, 360581283161933872, 360581283162305622, 360581282992783815, 360581284040252543, 360581285087743125, 360581285681720050, 360581286964976532]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 33240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 33200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk332A
