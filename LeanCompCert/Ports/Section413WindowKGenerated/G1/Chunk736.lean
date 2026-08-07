import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk736

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362465056853912240, 362465137560663053⟩, ⟨1479845413107162360, 1483856867092284666⟩, true⟩

def state01 : KState := ⟨⟨362487238644269954, 362487319373650397⟩, ⟨(-152848078840964822), (-148834959199458540)⟩, true⟩

def words00 : List Nat := [371285298387203494, 371285298211357181, 371285297972189556, 371285297895872878, 371285297818827610, 371285297699513802, 371285297448280375, 371285297382739344, 371285297431625060, 371285297461718764]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 73600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 73600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483032151148643, 362483112903597175⟩, ⟨156873005848137946, 160887823648458632⟩, true⟩

def words01 : List Nat := [371285297490004489, 371285297519169582, 371285297731589474, 371285297852634139, 371285298028787624, 371285298205940283, 371285298380765534, 371285298383295586, 371285298312158477, 371285298285608157]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 73610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 73600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362470809192633614, 362470889967602439⟩, ⟨1056811106797617406, 1060827582658926824⟩, true⟩

def words02 : List Nat := [371285298395100863, 371285298397631147, 371285298313251085, 371285298173322149, 371285298032412409, 371285297935509487, 371285297771382303, 371285297688892822, 371285297605593366, 371285297513204218]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 73620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 73600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489125438875787, 362489206236785596⟩, ⟨(-291927685414485600), (-287909520295811654)⟩, true⟩

def words03 : List Nat := [371285297319249777, 371285297264010468, 371285297207438648, 371285297200468668, 371285297027489038, 371285296824738945, 371285296620985994, 371285296602553966, 371285296544565893, 371285296600573489]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 73630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 73600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474282802149317, 362474363622879011⟩, ⟨801121474274022461, 805141319965482841⟩, true⟩

def words04 : List Nat := [371285296656056737, 371285296658587718, 371285296468234526, 371285296463365644, 371285296457278771, 371285296441729103, 371285296227354645, 371285295972155703, 371285295715900769, 371285295616361231]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 73640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 73600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362479033043307589, 362479113886805518⟩, ⟨451301757428599277, 455323280113507251⟩, true⟩

def words05 : List Nat := [371285295505362018, 371285295543798863, 371285295581918134, 371285295584493537, 371285295469021940, 371285295410974522, 371285295454768453, 371285295457311936, 371285295386312604, 371285295305215965]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 73650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 73600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471287051463277, 362471367917641980⟩, ⟨1021925493479546397, 1025948686947930523⟩, true⟩

def words06 : List Nat := [371285295223050613, 371285295173286993, 371285295030131583, 371285295023986450, 371285295017035080, 371285294984445546, 371285294705560741, 371285294491605014, 371285294276320269, 371285294192746473]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 73660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 73600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481583686000557, 362481664575260957⟩, ⟨263314727527885867, 267339621542690751⟩, true⟩

def words07 : List Nat := [371285294005614749, 371285293817980048, 371285293629297235, 371285293625748932, 371285293529759903, 371285293440634068, 371285293350678915, 371285293240789910, 371285293009249081, 371285292963175489]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 73670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 73600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481300160668555, 362481381072501686⟩, ⟨284283040133070478, 288309597423984808⟩, true⟩

def words08 : List Nat := [371285293050406186, 371285293073120673, 371285293096166230, 371285293120037373, 371285293199039188, 371285293201829875, 371285293327583921, 371285293469413737, 371285293535579888, 371285293538201564]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 73680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 73600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362500862896169525, 362500943830886671⟩, ⟨(-1157395201901730503), (-1153366958176403339)⟩, true⟩

def words09 : List Nat := [371285293584324646, 371285293684855938, 371285293968000959, 371285294006637109, 371285294008602230, 371285293999568037, 371285294098916246, 371285294130152361, 371285294344213446, 371285294559395424]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 73690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 73600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 73600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk736
