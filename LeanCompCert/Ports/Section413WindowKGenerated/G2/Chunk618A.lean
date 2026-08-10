import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk618A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585889025957927, 360585913398124948⟩, ⟨(-205412137052152816), (-204394630245713924)⟩, true⟩

def state01 : KState := ⟨⟨360583592376075963, 360583616756415136⟩, ⟨(-63506113589314578), (-62488101702553786)⟩, true⟩

def words00 : List Nat := [360582606270900959, 360582606370403200, 360582606371196733, 360582606270960271, 360582606170585831, 360582605961224398, 360582605914878768, 360582605948857614, 360582605949634849, 360582605802026718]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 61800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 61800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360612986390909165, 360613010779426674⟩, ⟨(-1880511316251276962), (-1879492798820733470)⟩, true⟩

def words01 : List Nat := [360582606027052406, 360582606252336674, 360582606738949424, 360582607072034784, 360582607180029823, 360582607288085361, 360582607389019141, 360582607620236157, 360582608112738344, 360582608605427213]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 61810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 61800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599936771036736, 360599961167816930⟩, ⟨(-1073837584916058296), (-1072818556646119738)⟩, true⟩

def words02 : List Nat := [360582608967192637, 360582609068430918, 360582609385825892, 360582609703482941, 360582609954902312, 360582610091099904, 360582610091872591, 360582610054091332, 360582610066112114, 360582610347732408]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 61820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 61800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574582565121110, 360574606970068631⟩, ⟨493872430086164541, 494891963383755755⟩, true⟩

def words03 : List Nat := [360582610474668068, 360582610601748877, 360582610602521219, 360582610598156839, 360582610430885906, 360582610159348051, 360582609887564578, 360582609878583711, 360582609879363323, 360582609750847800]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 61830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 61800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610267041792195, 360610291454927819⟩, ⟨(-1713051920799878057), (-1712031881110497269)⟩, true⟩

def words04 : List Nat := [360582609622143406, 360582609537283600, 360582609857378925, 360582610177630142, 360582610287710019, 360582610340139325, 360582610513913993, 360582610687945447, 360582611067915471, 360582611516347837]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 61840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 61800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk618A
