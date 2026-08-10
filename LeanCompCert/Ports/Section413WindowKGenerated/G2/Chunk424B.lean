import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk424A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk424B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk424A

def state06 : KState := ⟨⟨360559430260281100, 360559441419400425⟩, ⟨980509362778874057, 980829573948878025⟩, true⟩

def words05 : List Nat := [360582544912772793, 360582545222761385, 360582545223281515, 360582545201153417, 360582544626884182, 360582543670412765, 360582542713816448, 360582542311898208, 360582542047026258, 360582541503572561]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 42450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 42400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360631069886144657, 360631081050726434⟩, ⟨(-2061563467630595929), (-2061243024497693923)⟩, true⟩

def words06 : List Nat := [360582540970425473, 360582541417921849, 360582542419605622, 360582543421352880, 360582543943740259, 360582544284688919, 360582545179810352, 360582546075059030, 360582546954895371, 360582548098253036]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 42460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 42400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360631321261916515, 360631332432010266⟩, ⟨(-2072260791338090916), (-2071940114084562132)⟩, true⟩

def words07 : List Nat := [360582548783880019, 360582549469526617, 360582550709177952, 360582552224724477, 360582553600640532, 360582554976596066, 360582556074046539, 360582556797879464, 360582557946549676, 360582559095363658]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 42470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 42400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360650306643339867, 360650317818892251⟩, ⟨(-2878961536886500268), (-2878640627723772360)⟩, true⟩

def words08 : List Nat := [360582560498045408, 360582561821222346, 360582562648531703, 360582563475858986, 360582564055927969, 360582564985717852, 360582566469053665, 360582567952430613, 360582569156769164, 360582570751802191]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 42480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 42400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360660180503642981, 360660191684655296⟩, ⟨(-3298584809823921384), (-3298263668641000018)⟩, true⟩

def words09 : List Nat := [360582572900299981, 360582575048866162, 360582577281144774, 360582578962379891, 360582580176152020, 360582581389912269, 360582582380283385, 360582583653546449, 360582585480085865, 360582587306672637]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 42490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 42400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 42400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk424B
