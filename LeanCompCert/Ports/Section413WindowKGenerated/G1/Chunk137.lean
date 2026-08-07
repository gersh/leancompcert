import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk137

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492449468857378, 362492451898986432⟩, ⟨(-109626116874405746), (-109603592081486238)⟩, true⟩

def state01 : KState := ⟨⟨362547866496164852, 362547868930004953⟩, ⟨(-869288765667327661), (-869266190013839069)⟩, true⟩

def words00 : List Nat := [371284452806423485, 371284452806838189, 371284451923142087, 371284453759465756, 371284457236442684, 371284457906125261, 371284458543175350, 371284459180265002, 371284465122824580, 371284469747595659]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 13700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 13700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362452597958096643, 362452600395655734⟩, ⟨437719082956085509, 437741709615830471⟩, true⟩

def words01 : List Nat := [371284479676135178, 371284489603398568, 371284498526849727, 371284500377813061, 371284503100567023, 371284505823125469, 371284509726505370, 371284509726918262, 371284508093236737, 371284505768076713]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 13710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 13700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362493327816849836, 362493330258096893⟩, ⟨(-120965463502850654), (-120942786225643062)⟩, true⟩

def words02 : List Nat := [371284506417588016, 371284506748983624, 371284512379255841, 371284518008870915, 371284522612401029, 371284522612813263, 371284520154468552, 371284518873273413, 371284521606087919, 371284522248030209]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 13720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 13700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362471511483112722, 362471513928110826⟩, ⟨178916183034740935, 178938911833074739⟩, true⟩

def words03 : List Nat := [371284522681299972, 371284523114641114, 371284527969237406, 371284531042929373, 371284534671581744, 371284538299867583, 371284541718192286, 371284541718604852, 371284538085974624, 371284537138579027]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 13730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 13700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362413154418239772, 362413156866919454⟩, ⟨980861806532653217, 980884585934919291⟩, true⟩

def words04 : List Nat := [371284536349163296, 371284536349576059, 371284529461654760, 371284522594362940, 371284515727907916, 371284510486473633, 371284503269058604, 371284500157029322, 371284497045310232, 371284493927714721]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 13740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 13700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362563781156748890, 362563783609164664⟩, ⟨(-1091013341759728430), (-1090990510967412292)⟩, true⟩

def words05 : List Nat := [371284488830366484, 371284488920998308, 371284492259152441, 371284492259567985, 371284491439107954, 371284489286393350, 371284490253479913, 371284490744763537, 371284496507607241, 371284502269802161]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 13750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 13700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362501502079825669, 362501504535977006⟩, ⟨(-233767006785045472), (-233744124572373044)⟩, true⟩

def words06 : List Nat := [371284507090034699, 371284507577524158, 371284513334759336, 371284519091366996, 371284526471179795, 371284526828769224, 371284527056091339, 371284527283521564, 371284529653541257, 371284530886672499]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 13760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 13700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362450908016923821, 362450910476798134⟩, ⟨463497112216789988, 463520045713526030⟩, true⟩

def words07 : List Nat := [371284536558003265, 371284542228677070, 371284547893162740, 371284547893576531, 371284547960952698, 371284548420392195, 371284552487876536, 371284552488290340, 371284550076140527, 371284547635413049]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 13770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 13700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488033647584438, 362488036111164509⟩, ⟨(-48230084348897066), (-48207099767492604)⟩, true⟩

def words08 : List Nat := [371284548009171356, 371284548204383423, 371284548942806802, 371284549681287594, 371284549681608049, 371284549538823931, 371284543486622489, 371284540677155137, 371284540309440286, 371284540563360326]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 13780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 13700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493175599652514, 362493178067008900⟩, ⟨(-119063496465457673), (-119040459789846485)⟩, true⟩

def words09 : List Nat := [371284540808066849, 371284541052882807, 371284544744290744, 371284546995408791, 371284550281313531, 371284553566896001, 371284555938251731, 371284555938666125, 371284551946217355, 371284552571770161]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 13790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 13700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 13700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk137
