import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk868

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578332775128189, 360578382160384663⟩, ⟨327769663605888847, 330664472122189131⟩, true⟩

def state01 : KState := ⟨⟨360582042029206253, 360582091426243141⟩, ⟨5784244445649887, 8680075560217059⟩, true⟩

def words00 : List Nat := [360582191616044757, 360582191559955205, 360582191683478155, 360582191807237527, 360582191818708716, 360582191819957531, 360582191698665371, 360582191574308501, 360582191449587993, 360582191415594140]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 86800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 86800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360579631317943383, 360579680726876352⟩, ⟨215097362944012410, 217994226814400074⟩, true⟩

def words01 : List Nat := [360582191415557278, 360582191334810138, 360582191304331753, 360582191465867893, 360582191570185893, 360582191674705248, 360582191701768810, 360582191703017953, 360582191630055401, 360582191602559541]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 86810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 86800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360559828744680927, 360559878165390851⟩, ⟨1934377082730917702, 1937274969134619314⟩, true⟩

def words02 : List Nat := [360582191574666792, 360582191518224209, 360582191329091991, 360582191038914292, 360582190748542253, 360582190382836973, 360582190098386172, 360582189853632421, 360582189608725912, 360582189290222530]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 86820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 86800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360587949515021914, 360587998947523600⟩, ⟨(-507519817840962700), (-504620907500559112)⟩, true⟩

def words03 : List Nat := [360582189034284179, 360582188860016914, 360582188685372328, 360582188606378587, 360582188507047371, 360582188281054251, 360582188054823454, 360582187961407164, 360582188019145410, 360582188087359616]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 86830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 86800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577728323259630, 360577777767680193⟩, ⟨380126534747978661, 383026480183334419⟩, true⟩

def words04 : List Nat := [360582188089161711, 360582188094786099, 360582188232572483, 360582188370722776, 360582188422138058, 360582188423387584, 360582188371780988, 360582188253989119, 360582188135978279, 360582187974705908]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 86840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 86800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360560148492815521, 360560197949004024⟩, ⟨1907065512797860527, 1909966480336991367⟩, true⟩

def words05 : List Nat := [360582188006563750, 360582188089438272, 360582188090559894, 360582188070942956, 360582187918645698, 360582187704390682, 360582187489739625, 360582187407723046, 360582187223205992, 360582186971342696]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 86850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 86800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585790292067037, 360585839760071907⟩, ⟨(-320340643561352069), (-317438649595916157)⟩, true⟩

def words06 : List Nat := [360582186719201018, 360582186599814094, 360582186551532181, 360582186500045752, 360582186448463046, 360582186284253558, 360582186088697114, 360582185875055426, 360582185661035599, 360582185621756521]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 86860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 86800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579070376455070, 360579119856355379⟩, ⟨263470967721259671, 266373995102143677⟩, true⟩

def words07 : List Nat := [360582185622871628, 360582185581444972, 360582185604661438, 360582185737664129, 360582185828349626, 360582185919236391, 360582185920380350, 360582185911733983, 360582185889242520, 360582185855378194]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 86870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 86800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360567026713405599, 360567076205072447⟩, ⟨1309894203132004204, 1312798252849789072⟩, true⟩

def words08 : List Nat := [360582185897820569, 360582185899070657, 360582185844515860, 360582185723842100, 360582185602944165, 360582185449022163, 360582185361079676, 360582185255503080, 360582185149800047, 360582184943164861]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 86880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 86800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585152505848762, 360585202009334097⟩, ⟨(-265218429443054363), (-262313352758273647)⟩, true⟩

def words09 : List Nat := [360582184770311589, 360582184594408325, 360582184418136132, 360582184323360191, 360582184166957056, 360582183897331028, 360582183627471607, 360582183466723293, 360582183442404865, 360582183478445405]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 86890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 86800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 86800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk868
