import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk296

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362516408914130584, 362516421040791104⟩, ⟨(-912809404443958404), (-912566771424001136)⟩, true⟩

def state01 : KState := ⟨⟨362479832665441058, 362479844800669671⟩, ⟨169902641560358978, 170145528239256426⟩, true⟩

def words00 : List Nat := [371285592904636324, 371285592905586561, 371285592857618116, 371285593072059094, 371285593577404516, 371285593578352567, 371285592751645294, 371285591893444461, 371285591034909711, 371285591019117468]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 29600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 29600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476409067225154, 362476421210978332⟩, ⟨271495270102439730, 271738409238342694⟩, true⟩

def words01 : List Nat := [371285591770422403, 371285592716102958, 371285593666405448, 371285593869094536, 371285594419727150, 371285594970802299, 371285595996705051, 371285595997653612, 371285595672573060, 371285595363889823]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 29610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 29600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479742395650988, 362479754547891538⟩, ⟨172814519542313060, 173057910118048530⟩, true⟩

def words02 : List Nat := [371285595579754486, 371285595580799299, 371285596069669769, 371285596605919377, 371285596991421490, 371285596992370061, 371285595861333657, 371285595255117502, 371285595178368463, 371285595179350129]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 29620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 29600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362510135811367163, 362510147972278630⟩, ⟨(-727924079045710741), (-727680431508565405)⟩, true⟩

def words03 : List Nat := [371285594982962155, 371285594508173450, 371285594694202092, 371285594963258234, 371285595579843168, 371285596196740900, 371285596700970778, 371285596701937154, 371285597349242203, 371285598178698503]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 29630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 29600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478415711282970, 362478427880644786⟩, ⟨212484201302848759, 212728099351994183⟩, true⟩

def words04 : List Nat := [371285600143748429, 371285600594107260, 371285600926898361, 371285601259977430, 371285601455151160, 371285601456207805, 371285601582831987, 371285602049047031, 371285602520448889, 371285602521432375]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 29640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 29600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499740635810295, 362499752813751639⟩, ⟨(-419821084290989105), (-419576931814602447)⟩, true⟩

def words05 : List Nat := [371285603055617183, 371285603832218475, 371285605354225417, 371285605362942036, 371285605363684067, 371285605220251996, 371285605879951029, 371285606113503188, 371285606591122996, 371285607069110036]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 29650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 29600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491602633970974, 362491614820487053⟩, ⟨(-178540458291594821), (-178296051445626205)⟩, true⟩

def words06 : List Nat := [371285607552643851, 371285607553593617, 371285606628816776, 371285606734384055, 371285606905844906, 371285606906815706, 371285606439103055, 371285605753679770, 371285605515342567, 371285605718958772]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 29660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 29600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362494665649829506, 362494677844924976⟩, ⟨(-269344224904418177), (-269099563464468311)⟩, true⟩

def words07 : List Nat := [371285607055844539, 371285608393033742, 371285609463233358, 371285609464184278, 371285609358339713, 371285609478296056, 371285610520008093, 371285610840737633, 371285611146944383, 371285611453514159]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 29670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 29600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362502612737275032, 362502624940868640⟩, ⟨(-505057813647272105), (-504812899938126871)⟩, true⟩

def words08 : List Nat := [371285612728403776, 371285613539682200, 371285615483283339, 371285617427130823, 371285619178553261, 371285619419711723, 371285620134887836, 371285620850503892, 371285622147700807, 371285622721342921]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 29680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 29600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362506182272249749, 362506194484516598⟩, ⟨(-610992549655544397), (-610747378396268137)⟩, true⟩

def words09 : List Nat := [371285623278490261, 371285623835909536, 371285625196102972, 371285626132569270, 371285627414785079, 371285628697291963, 371285629933008265, 371285629933960130, 371285630598535100, 371285631292085493]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 29690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 29600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 29600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk296
