import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk267A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk267B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk267A

def state06 : KState := ⟨⟨360649043923461219, 360649048188238779⟩, ⟨(-1780277367467087687), (-1780200170881725661)⟩, true⟩

def words05 : List Nat := [360582509166209353, 360582509823374350, 360582511300303134, 360582513909998750, 360582516159404546, 360582518408699383, 360582519938606150, 360582521031424032, 360582523517775561, 360582526004057257]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360568156492544106, 360568160760635419⟩, ⟨384521880760310949, 384599166038748799⟩, true⟩

def words06 : List Nat := [360582528453611743, 360582529512178389, 360582529512493756, 360582529500187753, 360582529487825640, 360582528853434708, 360582528853720842, 360582528656301474, 360582528458852695, 360582527558022000]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360642661503188344, 360642665774599494⟩, ⟨(-1610481516809955475), (-1610404142643374853)⟩, true⟩

def words07 : List Nat := [360582527063189986, 360582527105112711, 360582527954928683, 360582528617101588, 360582528617435722, 360582527828147454, 360582527641121928, 360582528944992048, 360582531190864093, 360582533436649329]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360614543453623133, 360614547728387890⟩, ⟨(-857390326368320930), (-857312862375613618)⟩, true⟩

def words08 : List Nat := [360582534920523977, 360582536449456115, 360582539369448720, 360582542289330145, 360582544296302588, 360582545490455969, 360582545981997730, 360582546473541244, 360582546501320245, 360582547696198886]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360529616447504013, 360529620725584629⟩, ⟨1418378589245495522, 1418456142086376912⟩, true⟩

def words09 : List Nat := [360582549873131248, 360582552049969180, 360582553292673917, 360582553293025924, 360582553148886470, 360582552238733339, 360582551441294147, 360582551441646226, 360582550168187398, 360582548193572927]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk267B
