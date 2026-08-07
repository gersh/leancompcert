import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk280

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362447368670552660, 362447379471268369⟩, ⟨1056026805072687154, 1056231240059737248⟩, true⟩

def state01 : KState := ⟨⟨362488616190380186, 362488626999077022⟩, ⟨(-98955972341428144), (-98751313841480552)⟩, true⟩

def words00 : List Nat := [371285100668976561, 371285100596954526, 371285100484760819, 371285100919613029, 371285101151181252, 371285101152081503, 371285100577897889, 371285100533655978, 371285101424649830, 371285101551437114]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 28000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 28000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362499964272687309, 362499975089507159⟩, ⟨(-416805280788123313), (-416600394721079083)⟩, true⟩

def words01 : List Nat := [371285101677162313, 371285101803170893, 371285103064143592, 371285104015089210, 371285105195923206, 371285106377024879, 371285107332318216, 371285107333211108, 371285107122862415, 371285107654557619]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 28010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 28000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467666730069481, 362467677554856656⟩, ⟨488308787429959511, 488513896782415245⟩, true⟩

def words02 : List Nat := [371285108715066680, 371285108715959732, 371285108080780653, 371285107445567983, 371285106810053448, 371285106326421772, 371285105429936032, 371285105618071766, 371285105805690686, 371285105806614859]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 28020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 28000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491908632447289, 362491919465308917⟩, ⟨(-191240039786819110), (-191034704066517100)⟩, true⟩

def words03 : List Nat := [371285105834814315, 371285106485190710, 371285107776333316, 371285107777226632, 371285107566295505, 371285107015259500, 371285106691591981, 371285106692575921, 371285106529060453, 371285106773034515]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 28030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 28000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362466297728210010, 362466308569149751⟩, ⟨526982018540998360, 527187580811834136⟩, true⟩

def words04 : List Nat := [371285107000927261, 371285107001836119, 371285106276736616, 371285106378459270, 371285106785838689, 371285106786732786, 371285105741999889, 371285104697000504, 371285103651712525, 371285103135310601]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 28040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 28000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362467951191942462, 362467962040914834⟩, ⟨480776804718923810, 480982592345984330⟩, true⟩

def words05 : List Nat := [371285103065297892, 371285103665610650, 371285104271881587, 371285104272779617, 371285103759737588, 371285103575782905, 371285104475311835, 371285104476205655, 371285103869361456, 371285103259458882]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 28050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 28000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362458237853357380, 362458248710342733⟩, ⟨753373237610634423, 753579250123752557⟩, true⟩

def words06 : List Nat := [371285102688187933, 371285102689181713, 371285102099484331, 371285101833897119, 371285101568039170, 371285101102433031, 371285098946071596, 371285097254403448, 371285095562404122, 371285095138918571]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 28060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 28000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362460780848094471, 362460791713244278⟩, ⟨682042886933396128, 682249128661542752⟩, true⟩

def words07 : List Nat := [371285094183218184, 371285093222301572, 371285092343624255, 371285092344609365, 371285091795158810, 371285091644182825, 371285091492936731, 371285091112967578, 371285089198795082, 371285088334635359]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 28070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 28000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362453236992163462, 362453247865279492⟩, ⟨893971499444246571, 894177964905433385⟩, true⟩

def words08 : List Nat := [371285087871787549, 371285087872684052, 371285086979732164, 371285085715018324, 371285084450042189, 371285083332161734, 371285081668537163, 371285081271929167, 371285080875046890, 371285080473499693]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 28080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 28000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362512597417085764, 362512608298295628⟩, ⟨(-773860643326557290), (-773653950467810716)⟩, true⟩

def words09 : List Nat := [371285079340922254, 371285078736067108, 371285078359309704, 371285078360210828, 371285077460061132, 371285076362714712, 371285075432562532, 371285075433574801, 371285076128242287, 371285077108997461]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 28090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 28000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 28000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk280
