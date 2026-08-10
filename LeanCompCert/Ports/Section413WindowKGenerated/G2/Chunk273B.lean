import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk273A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk273B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk273A

def state06 : KState := ⟨⟨360595490329041940, 360595494795783787⟩, ⟨(-342472619209785443), (-342389957231950611)⟩, true⟩

def words05 : List Nat := [360582972032467358, 360582972852085090, 360582974117435605, 360582976259347258, 360582978059207392, 360582979859000684, 360582980636340131, 360582980636700194, 360582980542546249, 360582981000336547]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 27350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 27300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360620463527185731, 360620467997323783⟩, ⟨(-1026087594394269173), (-1026004839479189243)⟩, true⟩

def words06 : List Nat := [360582982790056389, 360582983251093319, 360582983251419722, 360582982684849603, 360582982118263751, 360582980797208412, 360582980827375426, 360582981508519397, 360582981521258924, 360582982891208582]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 27360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 27300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611338818875749, 360611343292413682⟩, ⟨(-776213990586829567), (-776131142600632253)⟩, true⟩

def words07 : List Nat := [360582985193233771, 360582987495195932, 360582990579675159, 360582992336621275, 360582992963949811, 360582993591260624, 360582994181992285, 360582995611312582, 360582996646949335, 360582997682589329]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 27370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 27300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573289128695369, 360573293605663020⟩, ⟨265462748808665485, 265545690717506025⟩, true⟩

def words08 : List Nat := [360582998047194093, 360582998047554486, 360582997147446612, 360582997209984802, 360582997210286588, 360582996931870545, 360582995326836498, 360582992780416701, 360582990234114008, 360582988592545733]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 27380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 27300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360517485155868120, 360517489636233638⟩, ⟨1794006670913186007, 1794089705906676681⟩, true⟩

def words09 : List Nat := [360582988238896102, 360582987171093722, 360582986103330487, 360582984175835770, 360582980922510469, 360582977329371475, 360582973736385932, 360582971472111936, 360582969752138294, 360582967362726583]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 27390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 27300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 27300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk273B
