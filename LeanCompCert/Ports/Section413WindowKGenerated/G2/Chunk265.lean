import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk265

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360540587188338556, 360540591367072242⟩, ⟨1115204612959186581, 1115279518178735469⟩, true⟩

def state01 : KState := ⟨⟨360604904256361842, 360604908438383679⟩, ⟨(-589374972083578816), (-589299979711890448)⟩, true⟩

def words00 : List Nat := [360582675798815840, 360582676565976059, 360582677969956136, 360582679373895895, 360582679664942671, 360582679665290775, 360582679238706127, 360582679219777393, 360582679200753324, 360582679930228126]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 26500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 26500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360593451482281096, 360593455667613751⟩, ⟨(-285604620756884529), (-285529540599058121)⟩, true⟩

def words01 : List Nat := [360582680053455960, 360582680176712358, 360582681718825527, 360582683974207592, 360582685864464483, 360582687754641356, 360582688929749849, 360582688930097790, 360582689093285409, 360582689499648778]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 26510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 26500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360577591129741123, 360577595318353695⟩, ⟨134888698429549621, 134963865587528379⟩, true⟩

def words02 : List Nat := [360582690123368252, 360582690123716280, 360582689835227586, 360582688431052326, 360582687026925949, 360582685251936374, 360582684193131959, 360582683955456132, 360582683717760585, 360582682535300078]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 26520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 26500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574530563703717, 360574534755601691⟩, ⟨215999990140223303, 216075244476156449⟩, true⟩

def words03 : List Nat := [360582683025440141, 360582683707382620, 360582684668198374, 360582684668546503, 360582684213239762, 360582682464492267, 360582680715815483, 360582678278186002, 360582676555779275, 360582676249364923]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 26530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 26500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360551086989275592, 360551091184493986⟩, ⟨837925989516649626, 838001331992544084⟩, true⟩

def words04 : List Nat := [360582675942926873, 360582674907639894, 360582673264792993, 360582671198926397, 360582669133117015, 360582666704060635, 360582663879732010, 360582660343018889, 360582656806505780, 360582654323175438]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 26540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 26500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk265
