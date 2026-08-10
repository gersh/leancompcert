import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk822A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360591795744618791, 360591839847813906⟩, ⟨(-784672604560250259), (-782224248135711681)⟩, true⟩

def state01 : KState := ⟨⟨360584148907565758, 360584193021863370⟩, ⟨(-156120024704268946), (-153670755597520758)⟩, true⟩

def words00 : List Nat := [360582323966210129, 360582324009955775, 360582324011013188, 360582323934213184, 360582323857223343, 360582323710739618, 360582323712515113, 360582323788076987, 360582323789126979, 360582323798090426]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360622462125085720, 360622506250507864⟩, ⟨(-3306083197625111040), (-3303633013918662452)⟩, true⟩

def words01 : List Nat := [360582323941378215, 360582324085019210, 360582324293642573, 360582324543088345, 360582324649839347, 360582324756648391, 360582325011096997, 360582325353239140, 360582325842891538, 360582326332799266]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604273409305312, 360604317545963881⟩, ⟨(-1810521983466915809), (-1808070875845806065)⟩, true⟩

def words02 : List Nat := [360582326748380957, 360582327171415060, 360582327742043511, 360582328313016285, 360582328739893605, 360582329019424909, 360582329224695652, 360582329430090139, 360582329573369997, 360582329842107115]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596742193669533, 360596786341424321⟩, ⟨(-1191154721142413538), (-1188702701023512370)⟩, true⟩

def words03 : List Nat := [360582330258272421, 360582330674655969, 360582331016586782, 360582331211131134, 360582331368355309, 360582331525919826, 360582331830908233, 360582332093588974, 360582332270396058, 360582332447368759]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360624568029374147, 360624612188270418⟩, ⟨(-3479720157979745028), (-3477267221532274632)⟩, true⟩

def words04 : List Nat := [360582332771867155, 360582333171758285, 360582333535386191, 360582333899214771, 360582334137017206, 360582334401459285, 360582334687883834, 360582334974643003, 360582335381902017, 360582335897142867]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk822A
