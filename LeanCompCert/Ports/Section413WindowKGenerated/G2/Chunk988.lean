import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk988

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360577319674492919, 360577384304330124⟩, ⟨494110708972626098, 498422336086900130⟩, true⟩

def state01 : KState := ⟨⟨360608285168719622, 360608349812102136⟩, ⟨(-2565439686613582198), (-2561126721156394440)⟩, true⟩

def words00 : List Nat := [360582429066223527, 360582429196921506, 360582429382487760, 360582429568328458, 360582429656315048, 360582429664695990, 360582429775152811, 360582429886031536, 360582430098833245, 360582430362636425]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 98800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 98800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585043671650070, 360585108328733579⟩, ⟨(-268799223186045131), (-264484903866620583)⟩, true⟩

def words01 : List Nat := [360582430574966400, 360582430787461988, 360582430967281887, 360582431209299923, 360582431424998516, 360582431640927203, 360582431805377205, 360582431867886694, 360582431896154411, 360582431924893640]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 98810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 98800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578807011483810, 360578871682090631⟩, ⟨347501361573415733, 351817017333742633⟩, true⟩

def words02 : List Nat := [360582431988055864, 360582431989491925, 360582431950678267, 360582431860727221, 360582431770535673, 360582431627706964, 360582431566157773, 360582431564167454, 360582431562031393, 360582431502158766]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 98820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 98800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583866516639729, 360583931200826341⟩, ⟨(-152603184268491388), (-148286186352082092)⟩, true⟩

def words03 : List Nat := [360582431479969199, 360582431494220544, 360582431504472461, 360582431505908645, 360582431414249029, 360582431219930218, 360582431025339937, 360582430933483164, 360582430934376669, 360582430951068123]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 98830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 98800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583040138120187, 360583104835969054⟩, ⟨(-71017500565341649), (-66699152203315769)⟩, true⟩

def words04 : List Nat := [360582430952347967, 360582430910285243, 360582430791367140, 360582430748137908, 360582430704528865, 360582430620411739, 360582430520515405, 360582430341212790, 360582430161638377, 360582430091634619]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 98840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 98800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360561551920207940, 360561616631585128⟩, ⟨2053276628357765114, 2057596314062295720⟩, true⟩

def words05 : List Nat := [360582430161378553, 360582430231402935, 360582430245415289, 360582430296078430, 360582430297283776, 360582430287862957, 360582430278016428, 360582430227412763, 360582430074640699, 360582429865593446]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 98850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 98800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575680920865304, 360575745645819448⟩, ⟨656367654550735018, 660688682539531728⟩, true⟩

def words06 : List Nat := [360582429656245727, 360582429415597658, 360582429225547307, 360582429119154636, 360582429012670383, 360582428818754475, 360582428522568967, 360582428329078739, 360582428135131754, 360582428043741361]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 98860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 98800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567936911230686, 360568001649865337⟩, ⟨1422087939370152560, 1426410320018149520⟩, true⟩

def words07 : List Nat := [360582427977434137, 360582427860030454, 360582427742349745, 360582427762246084, 360582427763470911, 360582427729652868, 360582427695677348, 360582427595614558, 360582427464830319, 360582427320577495]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 98870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 98800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582391564095088, 360582456316274159⟩, ⟨(-7271465264660299), (-2947745277547027)⟩, true⟩

def words08 : List Nat := [360582427175849894, 360582427105064640, 360582427038935216, 360582426921768307, 360582426804368965, 360582426661461882, 360582426577791785, 360582426587909946, 360582426589215937, 360582426508250401]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 98880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 98800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360604831684973075, 360604896450708177⟩, ⟨(-2226542632460111576), (-2222217571851082232)⟩, true⟩

def words09 : List Nat := [360582426540334179, 360582426572849731, 360582426707104611, 360582426759280699, 360582426760608891, 360582426725537612, 360582426755804722, 360582426882417919, 360582427110774398, 360582427339457016]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 98890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 98800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 98800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk988
