import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk628A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360537191934348495, 360537217133765954⟩, ⟨2852968293927862334, 2854037339593851146⟩, true⟩

def state01 : KState := ⟨⟨360578343506649694, 360578368714387824⟩, ⟨268421334374157998, 269490902619979392⟩, true⟩

def words00 : List Nat := [360582662865272825, 360582662395910747, 360582662054349319, 360582661787722783, 360582661521021004, 360582661032162654, 360582660394075118, 360582659959949015, 360582659525578093, 360582659287586678]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 62800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 62800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360583366445267427, 360583391661421740⟩, ⟨(-47169080256311430), (-46098983349295642)⟩, true⟩

def words01 : List Nat := [360582659220084182, 360582658954331042, 360582658688418069, 360582658566234788, 360582658566974908, 360582658441447293, 360582658315823182, 360582658062914801, 360582657833864803, 360582657846561275]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 62810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 62800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360577301067761119, 360577326292214894⟩, ⟨333807206134886822, 334877824455598064⟩, true⟩

def words02 : List Nat := [360582657897836145, 360582657898718323, 360582657771127356, 360582657495802516, 360582657220356265, 360582656766378322, 360582656473901073, 360582656434663004, 360582656395341617, 360582656195516750]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 62820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 62800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583677861034997, 360583703093829397⟩, ⟨(-66856046078259000), (-65784903675401498)⟩, true⟩

def words03 : List Nat := [360582656220579326, 360582656330752535, 360582656549788323, 360582656586684976, 360582656587498768, 360582656385871120, 360582656184080177, 360582656212009252, 360582656229394771, 360582656246967072]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 62830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 62800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577914970721250, 360577940211915316⟩, ⟨295182260696326678, 296253930976615438⟩, true⟩

def words04 : List Nat := [360582656247753163, 360582656138021279, 360582655953038715, 360582655717052615, 360582655480840254, 360582655180881513, 360582654928189241, 360582654549690583, 360582654171036889, 360582653878279304]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 62840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 62800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk628A
