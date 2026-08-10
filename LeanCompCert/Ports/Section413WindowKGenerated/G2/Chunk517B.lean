import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk517A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk517B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk517A

def state06 : KState := ⟨⟨360541798833861665, 360541815688366872⟩, ⟨2076696661061390751, 2077286122271125091⟩, true⟩

def words05 : List Nat := [360581953420287667, 360581953333927732, 360581953247496012, 360581952926663992, 360581952326729082, 360581951480661542, 360581950634415148, 360581950063224933, 360581949502464967, 360581948727823424]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360610866124079673, 360610882985345029⟩, ⟨(-1498625324821001924), (-1498035513672953208)⟩, true⟩

def words06 : List Nat := [360581947953049627, 360581947472518739, 360581947180438953, 360581947098577723, 360581947016677716, 360581946538428934, 360581946207183768, 360581946228286271, 360581946621580404, 360581947181252527]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360568206597868194, 360568223465963346⟩, ⟨710180735434031155, 710770900195033057⟩, true⟩

def words07 : List Nat := [360581947553878460, 360581947926580909, 360581948471698296, 360581949205507878, 360581949758867490, 360581950312320652, 360581950579955857, 360581950580672427, 360581950476100381, 360581950211814931]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586218432270753, 360586235307112232⟩, ⟨(-222586984110993269), (-221996469991439889)⟩, true⟩

def words08 : List Nat := [360581949947302137, 360581949937269706, 360581949805385117, 360581949436499980, 360581949067512211, 360581948605975633, 360581948640988935, 360581948844991256, 360581948845629895, 360581948916233674]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360607984691492624, 360608001573111622⟩, ⟨(-1349968478258348386), (-1349377613099077978)⟩, true⟩

def words09 : List Nat := [360581949261982682, 360581949607932220, 360581949912207415, 360581950248750007, 360581950268646808, 360581950288593611, 360581950680405345, 360581951307999038, 360581951811484929, 360581952315122412]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk517B
