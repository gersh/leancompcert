import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk718

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360555026810575199, 360555060103750182⟩, ⟨1957054620499780597, 1958669249977677083⟩, true⟩

def state01 : KState := ⟨⟨360605083651086079, 360605116953878847⟩, ⟨(-1637333532608534868), (-1635718212525141908)⟩, true⟩

def words00 : List Nat := [360582339240659974, 360582338947739796, 360582338751941682, 360582338686327807, 360582338620635819, 360582338389633202, 360582338267997327, 360582338304679752, 360582338534601521, 360582338852856370]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 71800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 71800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580517519829029, 360580550832351544⟩, ⟨126895265759527048, 128511284581281134⟩, true⟩

def words01 : List Nat := [360582339052740211, 360582339252725712, 360582339448492149, 360582339742073284, 360582339956546697, 360582340171180419, 360582340261471287, 360582340262490545, 360582340208402284, 360582340184684896]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 71810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 71800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360565076063537374, 360565109385653932⟩, ⟨1235967562725840871, 1237584270640265673⟩, true⟩

def words02 : List Nat := [360582340329170877, 360582340330190137, 360582340306217202, 360582340171879240, 360582340037386155, 360582339756301088, 360582339572410506, 360582339336588361, 360582339100671588, 360582338736491191]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 71820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 71800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360601086149841088, 360601119481573176⟩, ⟨(-1350832172439652975), (-1349214773793846397)⟩, true⟩

def words03 : List Nat := [360582338497455934, 360582338417604426, 360582338362556437, 360582338397652147, 360582338398592465, 360582338268504365, 360582338200534316, 360582338389005744, 360582338651261297, 360582338913738739]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 71830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 71800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598637448293756, 360598670789743962⟩, ⟨(-1175030201378307893), (-1173412104534194731)⟩, true⟩

def words04 : List Nat := [360582338996019357, 360582339013896567, 360582339224955093, 360582339436306882, 360582339598303504, 360582339599323126, 360582339568055831, 360582339439487443, 360582339374459478, 360582339602919364]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 71840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 71800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360578618314855097, 360578651665908099⟩, ⟨263451225532724812, 265070012385828462⟩, true⟩

def words05 : List Nat := [360582339888625532, 360582340174523500, 360582340341045028, 360582340398450289, 360582340399318713, 360582340322800897, 360582340328105752, 360582340415696550, 360582340416607765, 360582340366330947]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 71850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 71800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594683067824984, 360594716428516020⟩, ⟨(-890983709706387323), (-889364230217078071)⟩, true⟩

def words06 : List Nat := [360582340457785385, 360582340775016081, 360582341067478279, 360582341360126611, 360582341488211202, 360582341489231156, 360582341551149555, 360582341679452253, 360582341803413788, 360582341976647853]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 71860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 71800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592408252201451, 360592441622610497⟩, ⟨(-727485908173927624), (-725865730204971544)⟩, true⟩

def words07 : List Nat := [360582342053168230, 360582342129797619, 360582342322405180, 360582342661623367, 360582342900832455, 360582343140219516, 360582343232841123, 360582343233861362, 360582343322473579, 360582343464123485]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 71870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 71800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600103316683318, 360600136696710083⟩, ⟨(-1280708422541032669), (-1279087553202295809)⟩, true⟩

def words08 : List Nat := [360582343798617142, 360582343983646331, 360582344010877477, 360582344038194223, 360582344039053900, 360582343941219311, 360582344131731424, 360582344324171740, 360582344408063248, 360582344656632712]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 71880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 71800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360605586723736223, 360605620113391310⟩, ⟨(-1675020684965772330), (-1673399123399055654)⟩, true⟩

def words09 : List Nat := [360582344906324667, 360582345156318288, 360582345472144498, 360582345647959654, 360582345658857550, 360582345669843896, 360582345676615129, 360582345808341708, 360582346132870633, 360582346457622975]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 71890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 71800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 71800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk718
