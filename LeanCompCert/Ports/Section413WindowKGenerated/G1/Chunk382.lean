import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk382

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477177371004183, 362477198000344731⟩, ⟨297784718110742520, 298317260016110478⟩, true⟩

def state01 : KState := ⟨⟨362491960180654747, 362491980821166035⟩, ⟨(-266919377765699771), (-266386409080066289)⟩, true⟩

def words00 : List Nat := [371285007629728686, 371285007769528053, 371285008093312289, 371285008417568607, 371285008650598605, 371285008651868800, 371285008437301578, 371285008559203180, 371285009178704289, 371285009362447864]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 38200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 38200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492077556617215, 362492098208509902⟩, ⟨(-271413419426440711), (-270880015801462129)⟩, true⟩

def words01 : List Nat := [371285009517071380, 371285009672097144, 371285010026587340, 371285010147132608, 371285010474783977, 371285010802910513, 371285011129237703, 371285011130486837, 371285010817729106, 371285011004726604]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 38210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 38200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362464514359669164, 362464535022674320⟩, ⟨782265361250627059, 782799189652489387⟩, true⟩

def words02 : List Nat := [371285011722278755, 371285011723528988, 371285011702659925, 371285011676378888, 371285011649612396, 371285011642840397, 371285011360603881, 371285011263401447, 371285011165791205, 371285011067394501]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 38220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 38200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362514327257079309, 362514347931392980⟩, ⟨(-1122345556593828351), (-1121811295811349085)⟩, true⟩

def words03 : List Nat := [371285010681158669, 371285010831175186, 371285011247901624, 371285011249172768, 371285011099255412, 371285010841416612, 371285011007879206, 371285011092495887, 371285011860520785, 371285012629078414]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 38230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 38200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485575592143320, 362485596277755695⟩, ⟨(-22828957703046712), (-22294264800457930)⟩, true⟩

def words04 : List Nat := [371285013253749161, 371285013254998914, 371285013262884543, 371285013558425599, 371285014060612470, 371285014061868271, 371285013910585545, 371285013584125755, 371285013419716062, 371285013436397288]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 38240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 38200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362479176574613118, 362479197271460611⟩, ⟨222017075121026502, 222552197825301208⟩, true⟩

def words05 : List Nat := [371285013958960099, 371285014481991526, 371285014945773795, 371285014947024928, 371285014645265701, 371285014383220184, 371285014418772481, 371285014420032278, 371285014259478114, 371285014108831895]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 38250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 38200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495196515738355, 362495217223785069⟩, ⟨(-390809647428059977), (-390274096183730635)⟩, true⟩

def words06 : List Nat := [371285014488678479, 371285014773444962, 371285015674820663, 371285016576668087, 371285017370358299, 371285017524426947, 371285018103773387, 371285018683733917, 371285019310386960, 371285019578147805]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 38260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 38200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362503325163152117, 362503345882607906⟩, ⟨(-701878822129077874), (-701342834203833248)⟩, true⟩

def words07 : List Nat := [371285019844375870, 371285020111038051, 371285021059702420, 371285021667854563, 371285022479365616, 371285023291323460, 371285024105438118, 371285024106689109, 371285024490383707, 371285024970557442]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 38270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 38200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362496205210558214, 362496225941169176⟩, ⟨(-429285479410025370), (-428749064406057186)⟩, true⟩

def words08 : List Nat := [371285026132243740, 371285026385550457, 371285026506627308, 371285026628096039, 371285026861767185, 371285026863159285, 371285027352363337, 371285027938914141, 371285028523701160, 371285028817448039]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 38280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 38200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362517877087001494, 362517897828894358⟩, ⟨(-1259253048372198913), (-1258716201325580913)⟩, true⟩

def words09 : List Nat := [371285029368478439, 371285029920107529, 371285031055964546, 371285031409206217, 371285031558546338, 371285031708268129, 371285032137824467, 371285032315765981, 371285033174722927, 371285034034180759]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 38290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 38200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 38200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk382
