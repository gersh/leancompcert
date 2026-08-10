import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk529A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360517167360326582, 360517184996708439⟩, ⟨3427051187540662446, 3427681566057092966⟩, true⟩

def state01 : KState := ⟨⟨360595992677255601, 360596010320558570⟩, ⟨(-743238618925568186), (-742607874247613494)⟩, true⟩

def words00 : List Nat := [360581979265199071, 360581978397802115, 360581977708052912, 360581977375044475, 360581977041989511, 360581976403611415, 360581975774311800, 360581975430861495, 360581975087209221, 360581975282962464]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 52900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 52900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360575343512317853, 360575361162614491⟩, ⟨349385313658211826, 350016428405720466⟩, true⟩

def words01 : List Nat := [360581975370432487, 360581975457973268, 360581975536456647, 360581975795059812, 360581975876619227, 360581975958293981, 360581975958947947, 360581975834561997, 360581975353791693, 360581975229666754]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 52910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 52900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360540459447719865, 360540477104921470⟩, ⟨2195520497259852080, 2196151977453025828⟩, true⟩

def words02 : List Nat := [360581975105285509, 360581974867681476, 360581974400309222, 360581973649473400, 360581972898547525, 360581971963009445, 360581971207057840, 360581970442408095, 360581969677713206, 360581968734950812]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 52920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 52900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360601156282128312, 360601173946257986⟩, ⟨(-1017530374403093031), (-1016898527473391789)⟩, true⟩

def words03 : List Nat := [360581967951662907, 360581967378558271, 360581966805254981, 360581966458024642, 360581966231405787, 360581965700028057, 360581965168526414, 360581965071910046, 360581965435345816, 360581965798934109]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 52930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 52900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360571761873247912, 360571779544375426⟩, ⟨538593058292828558, 539225275722584440⟩, true⟩

def words04 : List Nat := [360581965886512918, 360581965887246995, 360581965720287357, 360581965607911551, 360581965495345633, 360581965293201982, 360581964928821739, 360581964321649797, 360581963714349669, 360581963213416457]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 52940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 52900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk529A
