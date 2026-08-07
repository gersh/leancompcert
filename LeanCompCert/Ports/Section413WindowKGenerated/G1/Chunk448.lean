import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk448

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480080138101536, 362480108881439885⟩, ⟨242177626693404596, 243047667725418500⟩, true⟩

def state01 : KState := ⟨⟨362486025051248618, 362486053807837493⟩, ⟨(-24112803234196932), (-23242168510266850)⟩, true⟩

def words00 : List Nat := [371285534241847704, 371285534369507834, 371285534753339567, 371285535137738397, 371285535423410441, 371285535424893579, 371285535132419240, 371285534964435110, 371285535123676020, 371285535136785514]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 44800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 44800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496042324891521, 362496071094990555⟩, ⟨(-473010848848699052), (-472139608667080794)⟩, true⟩

def words01 : List Nat := [371285535141467791, 371285535146624984, 371285535532520547, 371285535784214444, 371285536185967279, 371285536588288406, 371285536990287332, 371285536991770470, 371285536965337834, 371285537202202196]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 44810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 44800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362462025047625993, 362462053830949693⟩, ⟨1051808456398715183, 1052680289378659613⟩, true⟩

def words02 : List Nat := [371285537558009677, 371285537559493111, 371285537331717180, 371285537040661246, 371285536749038920, 371285536459993326, 371285535951596734, 371285535796318660, 371285535640546695, 371285535434549485]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 44820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 44800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499160166458034, 362499188963204839⟩, ⟨(-613144058770421011), (-612271623966684453)⟩, true⟩

def words03 : List Nat := [371285534911775941, 371285534824529199, 371285535084862850, 371285535086347845, 371285534900146427, 371285534579679112, 371285534261156253, 371285534262806963, 371285534375795268, 371285534681989731]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 44830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 44800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483394172158856, 362483422982309595⟩, ⟨93901458462758115, 94774494366672531⟩, true⟩

def words04 : List Nat := [371285534987867921, 371285534989377491, 371285535270076484, 371285535660161879, 371285536200134979, 371285536234905960, 371285536236034634, 371285536158690425, 371285536124292207, 371285536125996701]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 44840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 44800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362484285363793327, 362484314187288920⟩, ⟨54016039063993987, 54889673553438155⟩, true⟩

def words05 : List Nat := [371285536529625230, 371285536980937900, 371285537432027308, 371285537433512167, 371285537334295088, 371285537361334263, 371285537797489007, 371285537798983335, 371285537790120158, 371285537764496978]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 44850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 44800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483728036487698, 362483756873280940⟩, ⟨79052502747897655, 79926733839185145⟩, true⟩

def words06 : List Nat := [371285538163302735, 371285538342029000, 371285538504098940, 371285538666759619, 371285538747163455, 371285538748648133, 371285538167004861, 371285538082601078, 371285538167323444, 371285538168886895]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 44860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 44800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489993196884574, 362490022047225825⟩, ⟨(-202087295978858676), (-201212456922714328)⟩, true⟩

def words07 : List Nat := [371285538130299040, 371285538092566502, 371285538367173936, 371285538445451655, 371285538661965370, 371285538879030124, 371285538995738108, 371285538997226366, 371285538701835516, 371285538803605525]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 44870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 44800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481210415593050, 362481239279141802⟩, ⟨192137187174159463, 193012619052383287⟩, true⟩

def words08 : List Nat := [371285539287581229, 371285539289066394, 371285539111727259, 371285538932956208, 371285538753610985, 371285538695837591, 371285538578648176, 371285538769181530, 371285538957244491, 371285538958782087]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 44880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 44800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490853366623208, 362490882243605118⟩, ⟨(-240827317433501169), (-239951282473836877)⟩, true⟩

def words09 : List Nat := [371285538864034476, 371285538815181216, 371285539210852900, 371285539212338274, 371285538997658305, 371285538690989914, 371285538383713596, 371285538280196407, 371285538115390536, 371285538236066894]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 44890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 44800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 44800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk448
