import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk806

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569166153448870, 360569208491584134⟩, ⟨1039935666054082636, 1042240341701127726⟩, true⟩

def state01 : KState := ⟨⟨360560893199274148, 360560935548379725⟩, ⟨1706673156420075160, 1708978716328849588⟩, true⟩

def words00 : List Nat := [360582139353788605, 360582139101788169, 360582138730262447, 360582138512791962, 360582138295026653, 360582137965295833, 360582137546240138, 360582137033594828, 360582136520733573, 360582136127914881]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 80600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 80600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360538197713682184, 360538240073667254⟩, ⟨3536362881836321007, 3538669318795189541⟩, true⟩

def words01 : List Nat := [360582135865848789, 360582135757698092, 360582135649419211, 360582135437268525, 360582135173742738, 360582134829060002, 360582134484049209, 360582134207660453, 360582133811153850, 360582133267896915]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 80610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 80600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591319414995296, 360591361785868636⟩, ⟨(-746612642981246176), (-744305328156280710)⟩, true⟩

def words02 : List Nat := [360582132724390861, 360582132334880754, 360582132022868950, 360582131800261469, 360582131577571671, 360582131220556531, 360582130927737442, 360582130788872258, 360582130663146306, 360582130778834663]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 80620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 80600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577900137386111, 360577942519269266⟩, ⟨335435899207290645, 337744101808909979⟩, true⟩

def words03 : List Nat := [360582130783617797, 360582130788513296, 360582130789462291, 360582130880215800, 360582130932413353, 360582130984800312, 360582130985828351, 360582130961383481, 360582130864769807, 360582130814182571]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 80630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 80600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360558303363320136, 360558345756058204⟩, ⟨1915804185003269308, 1918113263000500426⟩, true⟩

def words04 : List Nat := [360582130763184169, 360582130735990075, 360582130600783358, 360582130388904186, 360582130176842114, 360582129915024828, 360582129729842471, 360582129498114035, 360582129266274036, 360582128933528762]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 80640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 80600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360597693351784091, 360597735755415536⟩, ⟨(-1261210260891578819), (-1258900304290819987)⟩, true⟩

def words05 : List Nat := [360582128639571605, 360582128499483731, 360582128359045692, 360582128321952644, 360582128292394602, 360582128140457068, 360582127988701018, 360582128067792640, 360582128262225472, 360582128456915756]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580006186096403, 360580048600733622⟩, ⟨165382713169689894, 167693557550479776⟩, true⟩

def words06 : List Nat := [360582128522412552, 360582128523567635, 360582128497171990, 360582128494730456, 360582128491990440, 360582128365234013, 360582128133692176, 360582127824873914, 360582127515821520, 360582127360589213]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588563142232713, 360588605567738581⟩, ⟨(-524914057414794681), (-522602336206342457)⟩, true⟩

def words07 : List Nat := [360582127463411436, 360582127592219966, 360582127644172871, 360582127737991115, 360582127738975247, 360582127727517306, 360582127856367761, 360582128014526320, 360582128095841889, 360582128177321924]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360614461638692689, 360614504075107091⟩, ⟨(-2614455286872277900), (-2612142685510224038)⟩, true⟩

def words08 : List Nat := [360582128411927139, 360582128781294532, 360582129303673290, 360582129826261988, 360582130193144020, 360582130406806008, 360582130773615262, 360582131140755005, 360582131503760588, 360582131906147601]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592532166413340, 360592574613825224⟩, ⟨(-844835246832319863), (-842521758029191221)⟩, true⟩

def words09 : List Nat := [360582132210850826, 360582132515667507, 360582132828598603, 360582133219141392, 360582133571133233, 360582133923332810, 360582134175880855, 360582134311714535, 360582134442022733, 360582134572710131]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk806
