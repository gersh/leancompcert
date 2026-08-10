import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk572A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360617581619407564, 360617602370153303⟩, ⟨(-2041710243768292391), (-2040908326247437249)⟩, true⟩

def state01 : KState := ⟨⟨360600257983508017, 360600278741841575⟩, ⟨(-1050821577860566378), (-1050019226278262708)⟩, true⟩

def words00 : List Nat := [360581923207469426, 360581923464497085, 360581924026948290, 360581924589637306, 360581924974941024, 360581925055814902, 360581925056525528, 360581924983391085, 360581924970152756, 360581925291870796]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 57200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 57200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360563768527170262, 360563789293021959⟩, ⟨1036844793022845507, 1037647574756748353⟩, true⟩

def words01 : List Nat := [360581925455662318, 360581925619585286, 360581925620306678, 360581925578709144, 360581925232488643, 360581924808619861, 360581924384532475, 360581924122639607, 360581923960309177, 360581923644206104]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 57210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 57200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360636771853155134, 360636792626540643⟩, ⟨(-3140748920628382874), (-3139945707774704942)⟩, true⟩

def words02 : List Nat := [360581923327933398, 360581923580069614, 360581924148842130, 360581924717748726, 360581925007885390, 360581925335791647, 360581925892899195, 360581926450223161, 360581927245533270, 360581928205024774]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 57220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 57200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590357374097478, 360590378155097788⟩, ⟨(-484118776479109241), (-483315127793262731)⟩, true⟩

def words03 : List Nat := [360581929012339067, 360581929819719827, 360581930600890568, 360581931534574000, 360581932390235470, 360581933245997641, 360581933947860421, 360581934345487168, 360581934493664702, 360581934642094989]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 57230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 57200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586396613999343, 360586417402512000⟩, ⟨(-257390041348028527), (-256585962617916679)⟩, true⟩

def words04 : List Nat := [360581935095383522, 360581935244531641, 360581935245242658, 360581935240671107, 360581935235964174, 360581935294973934, 360581935430814110, 360581935566800165, 360581935567517859, 360581935629920816]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 57240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 57200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk572A
