import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk277A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk277B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk277A

def state06 : KState := ⟨⟨360513475987331314, 360513480591417889⟩, ⟨1916294037499159196, 1916380484766123656⟩, true⟩

def words05 : List Nat := [360582517921584400, 360582520239215673, 360582521475617403, 360582521475983003, 360582521419144307, 360582520246405079, 360582519073639620, 360582518661836993, 360582516957074493, 360582514470552116]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 27750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 27700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360545913118517904, 360545917726061878⟩, ⟨1015719965709061688, 1015806508970759608⟩, true⟩

def words06 : List Nat := [360582511984127628, 360582509200984451, 360582507402383729, 360582506897173332, 360582506391971372, 360582504778804375, 360582501873168939, 360582500260760900, 360582498648365316, 360582497002582252]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 27760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 27700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360580794785925939, 360580799396952511⟩, ⟨46767284148440869, 46853924139226883⟩, true⟩

def words07 : List Nat := [360582495685732875, 360582493718583059, 360582491751504916, 360582491076971464, 360582491061368520, 360582490088894979, 360582489116445167, 360582487416003465, 360582486063591256, 360582486003293016]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 27770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 27700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585764415580879, 360585769030058830⟩, ⟨(-91483806074524911), (-91397070187354625)⟩, true⟩

def words08 : List Nat := [360582486258814105, 360582486259180432, 360582485910219524, 360582484565425519, 360582483220668157, 360582481546915095, 360582480917593184, 360582480966749802, 360582480967076020, 360582480300967133]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 27780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 27700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360646605553628314, 360646610171561354⟩, ⟨(-1782517685684672078), (-1782430853763331572)⟩, true⟩

def words09 : List Nat := [360582481710284013, 360582483119610198, 360582485819318757, 360582488152424134, 360582489281818957, 360582490411160376, 360582490629880320, 360582491646702642, 360582493953420667, 360582496260055893]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 27790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 27700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 27700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk277B
