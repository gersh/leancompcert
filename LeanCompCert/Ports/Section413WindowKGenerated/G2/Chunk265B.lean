import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk265A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk265B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk265A

def state06 : KState := ⟨⟨360543341229141453, 360543345427645563⟩, ⟨1043599868161350165, 1043675297889605587⟩, true⟩

def words05 : List Nat := [360582653134688212, 360582651909266702, 360582650683899743, 360582648615921141, 360582647149115073, 360582645105227335, 360582643061391795, 360582642431643886, 360582641910506772, 360582640431331166]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360634611359104135, 360634615560898618⟩, ⟨(-1380919594814780141), (-1380844077678270561)⟩, true⟩

def words06 : List Nat := [360582638952188384, 360582639705294640, 360582641509586187, 360582643313808705, 360582643618417075, 360582643618766058, 360582643554113627, 360582643934059051, 360582645516214096, 360582647472468440]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360616371599165592, 360616375804286523⟩, ⟨(-896094230656866642), (-896018625120103704)⟩, true⟩

def words07 : List Nat := [360582648429045117, 360582649385594518, 360582651754288427, 360582655011428782, 360582657901153124, 360582660790718740, 360582662972791303, 360582664278521034, 360582665547112430, 360582666815718746]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580666790331823, 360580670998740149⟩, ⟨53015686693642405, 53091379626066253⟩, true⟩

def words08 : List Nat := [360582668673331579, 360582669120345885, 360582669120656965, 360582668856561438, 360582668592430424, 360582667586980427, 360582667849961652, 360582668112989229, 360582668113300405, 360582667665894195]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360629045232732990, 360629049444442690⟩, ⟨(-1233792892249618168), (-1233717111517894348)⟩, true⟩

def words09 : List Nat := [360582668926122916, 360582670261441242, 360582671071509336, 360582671071858498, 360582670472615610, 360582668700715416, 360582666928881821, 360582667357565668, 360582669101535768, 360582670845460776]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk265B
