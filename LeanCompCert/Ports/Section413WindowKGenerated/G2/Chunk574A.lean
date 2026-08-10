import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk574A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586566107954112, 360586587009935183⟩, ⟨(-267339942033577353), (-266529358729880365)⟩, true⟩

def state01 : KState := ⟨⟨360581853300357404, 360581874209892189⟩, ⟨3327508803524703, 4138525728101923⟩, true⟩

def words00 : List Nat := [360581944014894751, 360581944460020524, 360581945137954135, 360581945816017521, 360581946222729861, 360581946326799890, 360581946350221516, 360581946373871219, 360581946374524720, 360581946297084806]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 57400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 57400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595688904837308, 360595709822001262⟩, ⟨(-791039016816588782), (-790227561864638234)⟩, true⟩

def words01 : List Nat := [360581946296549150, 360581946145446740, 360581946145720472, 360581946534917990, 360581946846461503, 360581947158124851, 360581947316635426, 360581947345253736, 360581947585582152, 360581947826183275]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 57410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 57400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583291824633169, 360583312749342982⟩, ⟨(-79269588395499102), (-78457700121951414)⟩, true⟩

def words02 : List Nat := [360581947941055214, 360581947941856091, 360581947754256737, 360581947413762320, 360581947073149414, 360581946654672360, 360581946554151381, 360581946656009243, 360581946656730107, 360581946628256427]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 57420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 57400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360601666924127675, 360601687856395138⟩, ⟨(-1134729159430294646), (-1133916837082968358)⟩, true⟩

def words03 : List Nat := [360581946628909303, 360581946572726562, 360581946683159724, 360581946821933341, 360581946822684733, 360581946667007982, 360581946511184558, 360581946619223164, 360581946963555447, 360581947308057140]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 57430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 57400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576875789833220, 360576896729740047⟩, ⟨289368481122982741, 290181242313001983⟩, true⟩

def words04 : List Nat := [360581947469362530, 360581947793634197, 360581948110862122, 360581948428311736, 360581948668258704, 360581948669059986, 360581948606750413, 360581948353140840, 360581948099398211, 360581947752234617]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 57440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 57400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk574A
