import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk414

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362500826756757469, 362500851145911154⟩, ⟨(-653061597643214124), (-652379328020863262)⟩, true⟩

def state01 : KState := ⟨⟨362482643561178769, 362482667962444247⟩, ⟨99832234555987297, 100515005669102419⟩, true⟩

def words00 : List Nat := [371285094379144091, 371285094490490638, 371285094537000642, 371285094583964258, 371285094639210811, 371285094640710166, 371285094727238881, 371285095014400173, 371285095273415186, 371285095274824569]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 41400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 41400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362509708536064347, 362509732949642873⟩, ⟨(-1020990747483534083), (-1020307466426957493)⟩, true⟩

def words01 : List Nat := [371285095741273815, 371285096267035862, 371285097374774414, 371285097706443742, 371285097854871659, 371285098003722019, 371285098679710731, 371285099144666747, 371285099740339100, 371285100336561901]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 41410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 41400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362500980136849016, 362501004562704141⟩, ⟨(-659488638952582601), (-658804849334947923)⟩, true⟩

def words02 : List Nat := [371285100932192790, 371285100933554553, 371285101114577104, 371285101414791190, 371285101894585911, 371285102060408377, 371285102224641231, 371285102389303792, 371285102923465310, 371285103308828180]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 41420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 41400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466531147702161, 362466555585850465⟩, ⟨768000855314605631, 768685154301446659⟩, true⟩

def words03 : List Nat := [371285104075877754, 371285104843451289, 371285105492027484, 371285105493389638, 371285105413630320, 371285105462667936, 371285105810384438, 371285105811746668, 371285105384083043, 371285104938029554]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 41430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 41400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488518433950936, 362488542884286949⟩, ⟨(-143187048875238941), (-142502244767342737)⟩, true⟩

def words04 : List Nat := [371285104491346222, 371285104470383004, 371285104425968715, 371285104695617045, 371285104870782650, 371285104872151105, 371285104615467515, 371285104557435060, 371285104951758745, 371285105036110371]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 41440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 41400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362497506278707938, 362497530741442483⟩, ⟨(-515722676180069910), (-515037358089247224)⟩, true⟩

def words05 : List Nat := [371285105059728928, 371285105083793876, 371285105688763916, 371285106117294270, 371285106720784342, 371285107324784186, 371285107925269326, 371285107926951118, 371285108227515982, 371285108528806772]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 41450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 41400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485636881526484, 362485661356412685⟩, ⟨(-23628950619041864), (-22943128657424962)⟩, true⟩

def words06 : List Nat := [371285109071242339, 371285109072605355, 371285108840541693, 371285108535887069, 371285108230713508, 371285108101745729, 371285107841417848, 371285108002795372, 371285108108573302, 371285108123342409]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 41460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 41400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362518033105750476, 362518057592966165⟩, ⟨(-1367248633822377288), (-1366562300497611648)⟩, true⟩

def words07 : List Nat := [371285108668426640, 371285109214226904, 371285110251612691, 371285110586621846, 371285110806947062, 371285111027654037, 371285111491967252, 371285111707021260, 371285112502206309, 371285113297975746]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 41470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 41400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488123646702653, 362488148146239026⟩, ⟨(-126481308212855360), (-125794463761250368)⟩, true⟩

def words08 : List Nat := [371285113975578033, 371285114170032938, 371285114745324586, 371285115321274881, 371285116071958242, 371285116073322262, 371285116050381102, 371285116027774984, 371285116222187906, 371285116296831655]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 41480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 41400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467408879549430, 362467433391363480⟩, ⟨733214965119225837, 733902319030888281⟩, true⟩

def words09 : List Nat := [371285116951142164, 371285117605975709, 371285118260219816, 371285118261584032, 371285118166300655, 371285118191873981, 371285118586405940, 371285118587770252, 371285118209212029, 371285117784593140]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 41490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 41400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 41400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk414
