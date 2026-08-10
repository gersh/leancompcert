import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk453A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586834977697362, 360586847747307471⟩, ⟨(-165096821599666074), (-164705915478014322)⟩, true⟩

def state01 : KState := ⟨⟨360578941236219886, 360578954011670037⟩, ⟨192459285854457053, 192850456559522661⟩, true⟩

def words00 : List Nat := [360583212380459331, 360583212381079490, 360583212340201233, 360583212054847147, 360583211769398028, 360583211050473188, 360583210595842025, 360583210612112679, 360583210612669065, 360583210256573139]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 45300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 45300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360623805928153932, 360623818709467857⟩, ⟨(-1840752547463579673), (-1840361111042383839)⟩, true⟩

def words01 : List Nat := [360583210163149462, 360583210057890199, 360583210235762853, 360583210236383282, 360583210173419032, 360583209706147842, 360583209257123648, 360583209667717621, 360583210564270573, 360583211460928717]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 45310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 45300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360625180218078745, 360625193005293390⟩, ⟨(-1903183345523991895), (-1902791641652670037)⟩, true⟩

def words02 : List Nat := [360583212113052929, 360583212848667120, 360583213922933859, 360583214997341270, 360583215680300017, 360583216009940417, 360583216035652113, 360583216061429919, 360583216573047089, 360583217499752973]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 45320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 45300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360568133927955084, 360568146721022668⟩, ⟨683044695541771586, 683436664756407006⟩, true⟩

def words03 : List Nat := [360583218264499393, 360583219029335817, 360583219471550430, 360583219707551418, 360583219820097341, 360583219932802606, 360583220531130605, 360583220644356882, 360583220644920978, 360583220313099343]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 45330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 45300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360657738454813714, 360657751253740103⟩, ⟨(-3380024297567645641), (-3379632062685601093)⟩, true⟩

def words04 : List Nat := [360583220134449147, 360583220671948818, 360583221694942674, 360583222718013177, 360583223328902001, 360583224118911916, 360583225275437587, 360583226432094178, 360583227944106965, 360583229588006479]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 45340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 45300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk453A
