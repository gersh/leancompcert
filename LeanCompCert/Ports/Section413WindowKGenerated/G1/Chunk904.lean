import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk904

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472053374713338, 362472177076628840⟩, ⟨1162288961935332890, 1169839295536063038⟩, true⟩

def state01 : KState := ⟨⟨362485953472598824, 362486077202729748⟩, ⟨(-94292466398482989), (-86739581978343691)⟩, true⟩

def words00 : List Nat := [371285117635792404, 371285117618451082, 371285117636481428, 371285117708971376, 371285117740516152, 371285117743679954, 371285117676036586, 371285117706096686, 371285117796941562, 371285117810819712]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 90400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 90400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481758781459149, 362481882540341975⟩, ⟨284999419356497249, 292554903383821885⟩, true⟩

def words01 : List Nat := [371285117823677712, 371285117837631729, 371285117938368317, 371285117979219357, 371285118040548205, 371285118103115209, 371285118164476015, 371285118167632263, 371285118083211034, 371285118051328304]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 90410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 90400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478218550187923, 362478342337158905⟩, ⟨605138933575990681, 612696957480460743⟩, true⟩

def words02 : List Nat := [371285118071734471, 371285118074893059, 371285117998862745, 371285117913536424, 371285117826976943, 371285117778656588, 371285117690961195, 371285117701159516, 371285117706638104, 371285117709905565]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 90420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 90400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489702575231649, 362489826390811266⟩, ⟨(-433453016856936390), (-425892405737041276)⟩, true⟩

def words03 : List Nat := [371285117637137273, 371285117628517645, 371285117656563539, 371285117659719981, 371285117550405552, 371285117422454765, 371285117293245485, 371285117287581659, 371285117271656764, 371285117327380554]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 90430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 90400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484741515217333, 362484865359279737⟩, ⟨15227634178608576, 22790821426863886⟩, true⟩

def words04 : List Nat := [371285117380196486, 371285117383374471, 371285117374728117, 371285117426693621, 371285117514511542, 371285117517669544, 371285117463887588, 371285117384029675, 371285117327127667, 371285117330771466]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 90440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 90400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362480622711456988, 362480746583901247⟩, ⟨387842463306818583, 395408217841071181⟩, true⟩

def words05 : List Nat := [371285117418198940, 371285117509664984, 371285117577584339, 371285117580813098, 371285117608443615, 371285117639212703, 371285117743287380, 371285117746446806, 371285117712254011, 371285117667450231]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483943298444592, 362484067199191562⟩, ⟨87449101014492345, 95017415954528505⟩, true⟩

def words06 : List Nat := [371285117623800383, 371285117627279851, 371285117615744603, 371285117664037075, 371285117680059688, 371285117683216956, 371285117536117587, 371285117471981175, 371285117460274625, 371285117463543884]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487429108596377, 362487553038134168⟩, ⟨(-227923220022407710), (-220352300238557926)⟩, true⟩

def words07 : List Nat := [371285117454295721, 371285117440874364, 371285117531366006, 371285117589482538, 371285117631071408, 371285117673783149, 371285117717150246, 371285117720314811, 371285117663904609, 371285117694799783]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490782646361703, 362490906604042958⟩, ⟨(-531320253162906077), (-523746786809221191)⟩, true⟩

def words08 : List Nat := [371285117845939783, 371285117918531613, 371285117990169344, 371285118062843691, 371285118171697686, 371285118239993949, 371285118399140754, 371285118559597084, 371285118703913993, 371285118771144557]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497835582843992, 362497959569036913⟩, ⟨(-1169585484555843300), (-1162009438036694822)⟩, true⟩

def words09 : List Nat := [371285118914429191, 371285119059308915, 371285119283849875, 371285119346670279, 371285119388759377, 371285119431914423, 371285119514865575, 371285119538199890, 371285119682220455, 371285119827619286]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk904
