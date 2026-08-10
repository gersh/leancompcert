import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk249A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360565614689097680, 360565618358449457⟩, ⟨453297440277689910, 453359249811943492⟩, true⟩

def state01 : KState := ⟨⟨360568033213844679, 360568036886259084⟩, ⟨392899505597164577, 392961391406259059⟩, true⟩

def words00 : List Nat := [360583825009844074, 360583825010169233, 360583823593018788, 360583821372834294, 360583819152773795, 360583815985779506, 360583814100848339, 360583813824054064, 360583813547246105, 360583812132802893]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 24900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 24900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607612281591184, 360607615957078081⟩, ⟨(-593471970984449875), (-593410008623999491)⟩, true⟩

def words01 : List Nat := [360583811704840326, 360583811910223558, 360583812068872412, 360583812069197717, 360583810627819229, 360583807566486319, 360583804505337065, 360583803050977904, 360583803356068546, 360583804311934468]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 24910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 24900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360626589639742873, 360626593318331478⟩, ⟨(-1066764756163221419), (-1066702716493296429)⟩, true⟩

def words02 : List Nat := [360583804312228709, 360583804176043732, 360583804497745263, 360583805461738640, 360583805993041326, 360583806504138216, 360583806504433155, 360583805775916699, 360583805403136104, 360583807119763700]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 24920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 24900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599685683336963, 360599689364990697⟩, ⟨(-395647633091302491), (-395585516992171375)⟩, true⟩

def words03 : List Nat := [360583810023671610, 360583812927409149, 360583815020914686, 360583817868342321, 360583820303544223, 360583822738636718, 360583825405048248, 360583827240096933, 360583827876401904, 360583828512699604]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 24930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 24900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360612739232988034, 360612742917720705⟩, ⟨(-721240141922308952), (-721177949019632406)⟩, true⟩

def words04 : List Nat := [360583829072954558, 360583830434067710, 360583833397973883, 360583836361704594, 360583837968630553, 360583837979920784, 360583837980186127, 360583837624366421, 360583837989566877, 360583839148371997]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 24940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 24900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk249A
