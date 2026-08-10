import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk394A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580262454525959, 360580272004790501⟩, ⟨82225160741528626, 82479488192482598⟩, true⟩

def state01 : KState := ⟨⟨360639827520069587, 360639837075376086⟩, ⟨(-2265108571730929458), (-2264854045602479026)⟩, true⟩

def words00 : List Nat := [360582365471376523, 360582366079681508, 360582366413863444, 360582366748121020, 360582366748612944, 360582366466080492, 360582366696153536, 360582367054651295, 360582368055641680, 360582369514400661]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 39400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 39400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360614090539635965, 360614100100023021⟩, ⟨(-1250717430879620080), (-1250462704501032412)⟩, true⟩

def words01 : List Nat := [360582370557019012, 360582371599638100, 360582372739130310, 360582374200769401, 360582375499570369, 360582376798394986, 360582377601524924, 360582377764455771, 360582378569614118, 360582379374914551]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 39410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 39400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360612033863917470, 360612043429328660⟩, ⟨(-1169644237580157265), (-1169389313124536957)⟩, true⟩

def words02 : List Nat := [360582380651874511, 360582381642420859, 360582382183238813, 360582382724099232, 360582382935160384, 360582383468012173, 360582384478067042, 360582385488172815, 360582386078709789, 360582386831394940]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 39420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 39400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360635534162017236, 360635543732472139⟩, ⟨(-2096600221215788555), (-2096345097861777919)⟩, true⟩

def words03 : List Nat := [360582387390415588, 360582387949557149, 360582388935749376, 360582389282404985, 360582389282900321, 360582388992632109, 360582388910854607, 360582389617592065, 360582390965744711, 360582392313951773]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 39430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 39400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360660323414041692, 360660332989578442⟩, ⟨(-3074550390100431948), (-3074295066293836954)⟩, true⟩

def words04 : List Nat := [360582393340473188, 360582394533345296, 360582396367552694, 360582398201824690, 360582399500926975, 360582400771914529, 360582401719883777, 360582402667858460, 360582404089950298, 360582406065893521]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 39440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 39400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk394A
