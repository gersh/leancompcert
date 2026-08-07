import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk012

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360410024807449545, 360410024813582716⟩, ⟨164900789080326801, 164900794096926879⟩, true⟩

def state01 : KState := ⟨⟨360370658304325564, 360370658310567808⟩, ⟨211147647572187164, 211147652720230678⟩, true⟩

def words00 : List Nat := [360547884019089969, 360547884019101499, 360547789715371683, 360547342940947025, 360546896908054697, 360546249970202802, 360546010597910122, 360545877486396791, 360545744595083331, 360545160502898578]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 1200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 1200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361313548870196308, 361313548876549010⟩, ⟨(-938418113262302264), (-938418107980046392)⟩, true⟩

def words01 : List Nat := [360545016405309285, 360544815066491609, 360545068798636685, 360545068798648359, 360544883641011168, 360544123669881272, 360543364947674671, 360543722700989975, 360544353706061459, 360544983677548154]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 1210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 1200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361111308266314513, 361111308272779591⟩, ⟨(-697415459902750215), (-697415454482833295)⟩, true⟩

def words02 : List Nat := [360545036412048493, 360545036412060317, 360545660903757963, 360546295442021994, 360546475318663112, 360546475318674909, 360546026609637449, 360545237529428664, 360544449733318953, 360544764442980377]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 1220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 1200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨359492546964379972, 359492546970957324⟩, ⟨1306657676136035183, 1306657681694624949⟩, true⟩

def words03 : List Nat := [360545863912216360, 360546961598049725, 360547701194867564, 360547815984859122, 360547815984869168, 360547487656826806, 360547467852802233, 360547467852814161, 360547153655121408, 360546303165872345]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 1230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 1200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360820101905693234, 360820101912384497⟩, ⟨(-348612210268572278), (-348612204568157238)⟩, true⟩

def words04 : List Nat := [360545454047272217, 360544717950476685, 360544391544188864, 360544109040774361, 360543826991179709, 360543002840062422, 360542270526519025, 360541709307114558, 360541212148717463, 360541435082194124]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 1240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 1200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361068528187128072, 361068528193935451⟩, ⟨(-663724265430099123), (-663724259583967611)⟩, true⟩

def words05 : List Nat := [360541435082205044, 360541324478729064, 360541214051792895, 360541396918276074, 360541554728118733, 360541712286873700, 360541712286884591, 360541537705085875, 360541762908537226, 360542180644701536]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 1250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 1200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨359514784815388900, 359514784822312105⟩, ⟨1299270248550685039, 1299270254543354931⟩, true⟩

def words06 : List Nat := [360542675992950457, 360542675992962700, 360542572521933837, 360542143373472121, 360541714903504157, 360540771955605407, 360540158185107935, 360539498819268989, 360538840492618500, 360537832266834432]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 1260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 1200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361450528536255790, 361450528543296102⟩, ⟨(-1173086290867347752), (-1173086284725359000)⟩, true⟩

def words07 : List Nat := [360537027351467241, 360536400762910449, 360535775158778447, 360535301867696249, 360535074451837860, 360534255247147955, 360533437325470093, 360533338328476158, 360534054883341598, 360534770319466782]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 1270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 1200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360646974184850280, 360646974192009773⟩, ⟨(-148143585522020677), (-148143579226876845)⟩, true⟩

def words08 : List Nat := [360534989794500817, 360534989794513291, 360534860332671400, 360535089816162649, 360535140813137342, 360535140813149853, 360534615007112575, 360533592061623412, 360532570703324146, 360532223162399489]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 1280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 1200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360036169095275369, 360036169102553667⟩, ⟨644261078753499468, 644261085202521702⟩, true⟩

def words09 : List Nat := [360532894382222675, 360533564563811863, 360533923470890843, 360533923470903418, 360533709227564549, 360533016404227270, 360532324649233832, 360532211871989608, 360532136065744929, 360531754552709453]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 1290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 1200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 1200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk012
