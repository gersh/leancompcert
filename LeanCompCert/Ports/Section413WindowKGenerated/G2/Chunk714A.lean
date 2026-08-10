import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk714A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582554139880434, 360582587048562397⟩, ⟨(-22215755477546634), (-20628655766012108)⟩, true⟩

def state01 : KState := ⟨⟨360570991366440449, 360571024284652322⟩, ⟨803398267299404385, 804986047495899071⟩, true⟩

def words00 : List Nat := [360582298171294095, 360582298172308907, 360582298122767625, 360582297975355896, 360582297827783336, 360582297630740830, 360582297531463431, 360582297402399377, 360582297273233016, 360582297020228515]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 71400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 71400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360612073173156329, 360612106100922890⟩, ⟨(-2130462000101337398), (-2128873537556165048)⟩, true⟩

def words01 : List Nat := [360582296901099442, 360582296940131011, 360582297174613303, 360582297414634229, 360582297471644373, 360582297528720721, 360582297652463970, 360582297875227704, 360582298293411915, 360582298711813859]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 71410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 71400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604239208407591, 360604272145836348⟩, ⟨(-1571052912736954082), (-1569463760069766932)⟩, true⟩

def words02 : List Nat := [360582298974031653, 360582299267167220, 360582299523273376, 360582299779674945, 360582299986819812, 360582300056625636, 360582300057529163, 360582300004032336, 360582300091480950, 360582300400234722]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 71420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 71400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360600432541855445, 360600465488822490⟩, ⟨(-1299074753886560379), (-1297484919851548001)⟩, true⟩

def words03 : List Nat := [360582300846203580, 360582301292353734, 360582301640136750, 360582302057213748, 360582302305038472, 360582302553105793, 360582302996501492, 360582303349662254, 360582303604794414, 360582303860067972]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 71430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 71400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360620694534164597, 360620727490712678⟩, ⟨(-2746596277554842064), (-2745005759005165334)⟩, true⟩

def words04 : List Nat := [360582304279932933, 360582304850731129, 360582305616780220, 360582306383002079, 360582306955470595, 360582307378308492, 360582307913907553, 360582308449793763, 360582308934602849, 360582309473344060]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 71440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 71400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk714A
