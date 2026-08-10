import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk634A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571089025232962, 360571114727954734⟩, ⟨732633475903050348, 733734280299670538⟩, true⟩

def state01 : KState := ⟨⟨360608836729932078, 360608862441062630⟩, ⟨(-1660853489896361559), (-1659752152341275839)⟩, true⟩

def words00 : List Nat := [360582687642044288, 360582687547035600, 360582687570829948, 360582687594798386, 360582687595627706, 360582687403567316, 360582687235539763, 360582687250009225, 360582687512644661, 360582687926351598]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 63400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 63400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360597128483257287, 360597154202885539⟩, ⟨(-918427374887418213), (-917325498451360219)⟩, true⟩

def words01 : List Nat := [360582688180346363, 360582688434429349, 360582688682033130, 360582689089177718, 360582689334044832, 360582689579044581, 360582689698871929, 360582689699763662, 360582689908277741, 360582690137379613]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 63410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 63400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582543857338792, 360582569585359123⟩, ⟨6651097093361428, 7753505795763114⟩, true⟩

def words02 : List Nat := [360582690614509219, 360582690982268242, 360582691198302773, 360582691414418835, 360582691494188617, 360582691761780220, 360582691823334103, 360582691885038487, 360582691885832655, 360582691822562273]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 63420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 63400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360623015625317663, 360623041361749495⟩, ⟨(-2560682639960333319), (-2559579697675109819)⟩, true⟩

def words03 : List Nat := [360582692017285120, 360582692214199381, 360582692610483666, 360582693091496397, 360582693361969615, 360582693632503779, 360582693870990497, 360582694259773718, 360582694896482965, 360582695533378645]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 63430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 63400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360607548313274426, 360607574058216961⟩, ⟨(-1579506912443697368), (-1578403430200018354)⟩, true⟩

def words04 : List Nat := [360582695970561187, 360582696160333323, 360582696598105141, 360582697036127318, 360582697411274607, 360582697539100411, 360582697541880952, 360582697544780346, 360582697722590903, 360582698115675473]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 63440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 63400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk634A
