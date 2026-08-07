import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk255

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362508517570902686, 362508526458986969⟩, ⟨(-583077761336297934), (-582924530067461704)⟩, true⟩

def state01 : KState := ⟨⟨362474118598748692, 362474127494023295⟩, ⟨294308742115244038, 294462156774917398⟩, true⟩

def words00 : List Nat := [371285669104901501, 371285669105707803, 371285668879564126, 371285668645520496, 371285668642876961, 371285668643777178, 371285669162252783, 371285669977718594, 371285670502078719, 371285670502912943]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 25500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 25500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362495481331130983, 362495490233699154⟩, ⟨(-250689556659288507), (-250535955903755823)⟩, true⟩

def words01 : List Nat := [371285670838661853, 371285671627243752, 371285673677684447, 371285673683093887, 371285673683735553, 371285673309055594, 371285673151743717, 371285673152631898, 371285672993125151, 371285673378720754]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 25510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 25500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362464124130531951, 362464133040375281⟩, ⟨549718578410766068, 549872364866146506⟩, true⟩

def words02 : List Nat := [371285673720815815, 371285673721636215, 371285673392633810, 371285673995416321, 371285675054609858, 371285675055416456, 371285674071146959, 371285672951000217, 371285671830617073, 371285671323370430]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 25520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 25500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362445913014663191, 362445921931769357⟩, ⟨1014844006590397780, 1014997978502373042⟩, true⟩

def words03 : List Nat := [371285670480309380, 371285670375123057, 371285670269682645, 371285670183169121, 371285668539477575, 371285667361108959, 371285666534884814, 371285666535691936, 371285664989663687, 371285663434451518]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 25530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 25500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474167234187734, 362474176158528560⟩, ⟨293164761122461564, 293318917843944528⟩, true⟩

def words04 : List Nat := [371285661879011329, 371285661855277514, 371285661329823332, 371285661079880549, 371285660829702298, 371285660399556957, 371285658182787905, 371285657198041491, 371285656350156805, 371285656351007776]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 25540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 25500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362453193157555041, 362453202089264731⟩, ⟨829127359604890730, 829281704638072682⟩, true⟩

def words05 : List Nat := [371285655902314315, 371285655203522179, 371285654504451746, 371285654151266050, 371285653037706672, 371285652256155883, 371285651474412614, 371285650395768778, 371285647868781864, 371285646600400806]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 25550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 25500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362437425028132611, 362437433967037877⟩, ⟨1232324127387514369, 1232478656377258229⟩, true⟩

def words06 : List Nat := [371285645591577885, 371285645592385702, 371285643815086600, 371285642028769532, 371285640242270549, 371285638919864197, 371285636837821414, 371285635949740508, 371285635061449854, 371285634149141016]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 25560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 25500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498835543962546, 362498844490174483⟩, ⟨(-338384312117681039), (-338229596259387643)⟩, true⟩

def words07 : List Nat := [371285632264747234, 371285630755553256, 371285629246069258, 371285629059109877, 371285627303195177, 371285625212472877, 371285623121578322, 371285622558339311, 371285622065652544, 371285622583436694]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 25570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 25500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474293267858271, 362474302221360213⟩, ⟨289378956866732174, 289533859240544168⟩, true⟩

def words08 : List Nat := [371285623091468406, 371285623092276834, 371285621565707118, 371285621566169220, 371285621566229389, 371285621335271165, 371285619746273032, 371285618174656392, 371285616602842343, 371285616557399313]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 25580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 25500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362424115790569003, 362424124751375103⟩, ⟨1573923110917048805, 1574078200240576553⟩, true⟩

def words09 : List Nat := [371285616962461614, 371285617809929316, 371285618631626412, 371285618632435438, 371285617684467105, 371285617199810812, 371285616714780338, 371285616664557116, 371285614582097643, 371285612181072001]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 25590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 25500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 25500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk255
