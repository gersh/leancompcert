import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk251A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587343667076353, 360587347398206008⟩, ⟨(-87785135382047430), (-87721781393052418)⟩, true⟩

def state01 : KState := ⟨⟨360547236241952455, 360547239976212676⟩, ⟨919111902551190080, 919175335132688390⟩, true⟩

def words00 : List Nat := [360583852646045189, 360583852270470242, 360583852998884845, 360583853727335909, 360583854051529370, 360583854051857441, 360583852797614503, 360583850744307782, 360583848691107348, 360583845923450139]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360529778158825677, 360529781896176643⟩, ⟨1357700651585217444, 1357764161790816028⟩, true⟩

def words01 : List Nat := [360583844589612650, 360583844713593435, 360583844713887834, 360583843638234191, 360583841768588933, 360583839495842014, 360583837223172066, 360583836531410362, 360583835168729681, 360583833017267042]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360608591402390170, 360608595142844551⟩, ⟨(-622536273639727475), (-622472685461021341)⟩, true⟩

def words02 : List Nat := [360583830865901765, 360583830680464679, 360583830680735072, 360583830425714785, 360583830170687458, 360583828502386962, 360583826338656566, 360583825754962101, 360583825171216300, 360583826025600470]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558130209980630, 360558133953559366⟩, ⟨645906295334064780, 645969962043235486⟩, true⟩

def words03 : List Nat := [360583826213159415, 360583826400739293, 360583827480385600, 360583829616168078, 360583830709029474, 360583831801855582, 360583831802156956, 360583831629500322, 360583829882301030, 360583828860561882]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579536890489884, 360579540637163194⟩, ⟨107563126560610672, 107626871082679268⟩, true⟩

def words04 : List Nat := [360583827838795927, 360583827735568475, 360583827202789244, 360583825424157982, 360583823645609286, 360583821188415404, 360583820290522398, 360583820630293908, 360583820630586793, 360583820035615786]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk251A
