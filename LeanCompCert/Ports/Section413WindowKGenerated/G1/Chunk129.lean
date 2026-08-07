import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk129

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482759272330661, 362482761415549294⟩, ⟨17781390891918800, 17800098474021302⟩, true⟩

def state01 : KState := ⟨⟨362366328659465570, 362366330806118297⟩, ⟨1520148110391899962, 1520166862291807076⟩, true⟩

def words00 : List Nat := [371284142083776108, 371284142084160957, 371284135017827775, 371284126006766656, 371284116996952546, 371284108805052553, 371284097629732601, 371284092442721648, 371284087256383060, 371284081918611853]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 12900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 12900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362522944419080479, 362522946569217293⟩, ⟨(-502536428165070161), (-502517631267989947)⟩, true⟩

def words01 : List Nat := [371284072798657574, 371284069665119107, 371284067839071349, 371284067839459123, 371284063848838772, 371284057896257703, 371284051973128967, 371284051973553149, 371284052015275795, 371284055025894951]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 12910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 12900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487094081082638, 362487096234703816⟩, ⟨(-39113109719950627), (-39094267786998395)⟩, true⟩

def words02 : List Nat := [371284057699909731, 371284057700303666, 371284062449554304, 371284067812116585, 371284073227235855, 371284073227622027, 371284072390131177, 371284071677041910, 371284072702339752, 371284072936599494]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 12920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 12900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362426346642559139, 362426348799653694⟩, ⟨747069741072704097, 747088627933968153⟩, true⟩

def words03 : List Nat := [371284078150917390, 371284083364581511, 371284088637557335, 371284088637943651, 371284087841058639, 371284088086808102, 371284092059901743, 371284092060287843, 371284088085717200, 371284083624068993]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 12930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 12900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362433448345927927, 362433450506485306⟩, ⟨655351498213847303, 655370429901756945⟩, true⟩

def words04 : List Nat := [371284080662963927, 371284080663392971, 371284079710097560, 371284080166949694, 371284080167249002, 371284079680443158, 371284071254897597, 371284065566520535, 371284059878825921, 371284058261690075]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 12940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 12900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362519111937407508, 362519114101493243⟩, ⟨(-454441971222454063), (-454422993825117027)⟩, true⟩

def words05 : List Nat := [371284054354349133, 371284050368002699, 371284048346256318, 371284048346682898, 371284049447021926, 371284050883394307, 371284051130771347, 371284051131161734, 371284050598394853, 371284053304191715]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 12950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 12900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362455761679028781, 362455763846558640⟩, ⟨366954087766044328, 366973109817525040⟩, true⟩

def words06 : List Nat := [371284059860729918, 371284059861116800, 371284058497598521, 371284056447181058, 371284054396929141, 371284054121071651, 371284053576978462, 371284056273287494, 371284057840747004, 371284057841147501]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 12960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 12900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362566391221376021, 362566393392410437⟩, ⟨(-1068672663440470009), (-1068653595917227473)⟩, true⟩

def words07 : List Nat := [371284055660088885, 371284054426473499, 371284057892304107, 371284057892693241, 371284057012516738, 371284055159339818, 371284055847206700, 371284056262818929, 371284062606466747, 371284068949307654]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 12970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 12900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491146676424219, 362491148850949228⟩, ⟨(-91824911687306172), (-91805798837960540)⟩, true⟩

def words08 : List Nat := [371284075288544662, 371284075288932207, 371284078097784518, 371284082464113141, 371284086990810062, 371284086991197817, 371284084852569037, 371284082122119281, 371284081429503947, 371284081973969938]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 12980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 12900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362403304759791096, 362403306937820551⟩, ⟨1049945608240170422, 1049964766629526180⟩, true⟩

def words09 : List Nat := [371284085530471520, 371284089086593819, 371284092141538164, 371284092141926200, 371284088550524749, 371284085813463291, 371284084734913262, 371284084735301442, 371284079671176306, 371284073458330515]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 12990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 12900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 12900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk129
