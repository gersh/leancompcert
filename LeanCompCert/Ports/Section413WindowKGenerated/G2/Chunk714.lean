import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk714

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

def state06 : KState := ⟨⟨360611606096553442, 360611639062758496⟩, ⟨(-2097154658881209321), (-2095563450292335419)⟩, true⟩

def words05 : List Nat := [360582309878432647, 360582310283609322, 360582310884123266, 360582311583532133, 360582312201608800, 360582312819858170, 360582313340130430, 360582313665084728, 360582314076281083, 360582314487811430]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 71450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 71400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589283700845100, 360589316676610536⟩, ⟨(-501983939219310749), (-500392047397907121)⟩, true⟩

def words06 : List Nat := [360582314869643610, 360582315056251155, 360582315077026289, 360582315097895030, 360582315098743647, 360582315156500693, 360582315220014371, 360582315283717336, 360582315284630102, 360582315346736911]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 71460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 71400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360626066675074756, 360626099660407279⟩, ⟨(-3131057317648753058), (-3129464742020244278)⟩, true⟩

def words07 : List Nat := [360582315640962149, 360582315935476524, 360582316425126225, 360582316857171951, 360582317120748607, 360582317384395547, 360582317643714845, 360582318061956787, 360582318675278018, 360582319288811747]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 71470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 71400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360604421142679972, 360604454137668238⟩, ⟨(-1583778985117785345), (-1582185719250579849)⟩, true⟩

def words08 : List Nat := [360582319804445598, 360582320179512875, 360582320749763855, 360582321320317909, 360582321749057328, 360582322061496733, 360582322243270379, 360582322425136264, 360582322569589746, 360582322880317655]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 71480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 71400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571551834858490, 360571584839411849⟩, ⟨766206812463419202, 767800762186323600⟩, true⟩

def words09 : List Nat := [360582323182261193, 360582323484376013, 360582323688676498, 360582323697851563, 360582323698700526, 360582323634078369, 360582323569151239, 360582323512356278, 360582323460737640, 360582323311610260]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 71490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 71400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 71400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk714
