import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk634

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

def state06 : KState := ⟨⟨360554163860743684, 360554189614079302⟩, ⟨1808111100074802350, 1809215114901872866⟩, true⟩

def words05 : List Nat := [360582698700111702, 360582699284700993, 360582699715183777, 360582699898338145, 360582699899098100, 360582699882723645, 360582699866089877, 360582699855677632, 360582699597788451, 360582699149454371]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595404972738953, 360595430734506025⟩, ⟨(-809245356727827579), (-808140806798563693)⟩, true⟩

def words06 : List Nat := [360582698700932457, 360582698337037733, 360582698240759188, 360582698317154155, 360582698317976632, 360582698184228587, 360582698016363924, 360582698057059028, 360582698091276335, 360582698292811416]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593614760840576, 360593640531095815⟩, ⟨(-695562258869834270), (-694457170154122232)⟩, true⟩

def words07 : List Nat := [360582698369359291, 360582698446002075, 360582698770406558, 360582699250445861, 360582699665577909, 360582700080857028, 360582700370198239, 360582700578025923, 360582700751089155, 360582700924439428]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585662969448533, 360585688748111304⟩, ⟨(-190889112167183719), (-189783489697940967)⟩, true⟩

def words08 : List Nat := [360582701050405225, 360582701051297362, 360582700930115183, 360582700618970217, 360582700307689389, 360582699934086381, 360582699686006205, 360582699685951090, 360582699685798014, 360582699608080466]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360611147588713198, 360611173375797316⟩, ⟨(-1809049333130720349), (-1807943175950060173)⟩, true⟩

def words09 : List Nat := [360582699855872210, 360582700103929635, 360582700599498891, 360582700932007614, 360582701032742121, 360582701133532993, 360582701178086428, 360582701379695213, 360582701828794584, 360582702278083106]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk634
