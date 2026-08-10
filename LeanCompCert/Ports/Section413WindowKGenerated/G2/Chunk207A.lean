import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk207A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360415084769511413, 360415087264208584⟩, ⟨3445422039991589127, 3445456984888899611⟩, true⟩

def state01 : KState := ⟨⟨360468582334680647, 360468584831882356⟩, ⟨2337685110964104303, 2337720107717458433⟩, true⟩

def words00 : List Nat := [360581526421222344, 360581520001416145, 360581513282570430, 360581505070519477, 360581496859218587, 360581487341491292, 360581480086002409, 360581475151060402, 360581470216569181, 360581463639594450]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 20700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 20700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360506364551896533, 360506367051610557⟩, ⟨1554699738892914177, 1554734787689142845⟩, true⟩

def words01 : List Nat := [360581458189623419, 360581454386310852, 360581450583293040, 360581445479885799, 360581438050585387, 360581428618602509, 360581419187479366, 360581412075226500, 360581406135634130, 360581402514336867]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 20710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 20700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360440827772502014, 360440830274750069⟩, ⟨2912610110034503703, 2912645211348337473⟩, true⟩

def words02 : List Nat := [360581398893346032, 360581394109028483, 360581388706817742, 360581382759957601, 360581376813599528, 360581370236200222, 360581362340359439, 360581352608502761, 360581342877534645, 360581334144086699]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 20720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 20700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360379511657794991, 360379514162550741⟩, ⟨4184340292519367078, 4184375445830419644⟩, true⟩

def words03 : List Nat := [360581327366825443, 360581322905286215, 360581318444148127, 360581312821629145, 360581307303665238, 360581299685001804, 360581292066992584, 360581286078099062, 360581277769286666, 360581268041327522]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 20730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 20700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360541757647935582, 360541760155210632⟩, ⟨818326901944336008, 818362107517916666⟩, true⟩

def words04 : List Nat := [360581258314249244, 360581248533600724, 360581239941072586, 360581233661411187, 360581227382336438, 360581219136024204, 360581211863063465, 360581206902208446, 360581201941746949, 360581199292922339]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 20740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 20700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk207A
