import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk448

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576361737111563, 360576374214979079⟩, ⟨304685698476956327, 305063461458710345⟩, true⟩

def state01 : KState := ⟨⟨360597186229085878, 360597198712733984⟩, ⟨(-628333280870219720), (-627955258889281854)⟩, true⟩

def words00 : List Nat := [360583183714902469, 360583184234855413, 360583184830809667, 360583185426852159, 360583185573919109, 360583185574532390, 360583185420592214, 360583185108745945, 360583184981706905, 360583185295071150]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 44800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 44800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360601645429311658, 360601657918804113⟩, ⟨(-828181050063142109), (-827802766168823841)⟩, true⟩

def words01 : List Nat := [360583185295625006, 360583185289329577, 360583185569260989, 360583186358466982, 360583187020527478, 360583187682658424, 360583188095014972, 360583188095628209, 360583188423091902, 360583188835870470]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 44810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 44800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360561014775294839, 360561027270570907⟩, ⟨992979435279728615, 993357978424410045⟩, true⟩

def words02 : List Nat := [360583189064728228, 360583189065341603, 360583188949679748, 360583188510806825, 360583188071854684, 360583187283593448, 360583186778051125, 360583186500382464, 360583186222655196, 360583185601564091]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 44820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 44800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360604447952357333, 360604460453421581⟩, ⟨(-954400830970801313), (-954022028313905405)⟩, true⟩

def words03 : List Nat := [360583185107796533, 360583184992071504, 360583185138686077, 360583185142735081, 360583185143310653, 360583184668543821, 360583184193679033, 360583183862017484, 360583184314776397, 360583184789892358]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 44830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 44800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599310472890582, 360599322979805371⟩, ⟨(-724041513417514763), (-723662448394621081)⟩, true⟩

def words04 : List Nat := [360583185015551981, 360583185258231446, 360583185997426685, 360583186736769065, 360583187349363546, 360583187798591286, 360583187854304685, 360583187910073352, 360583187910578287, 360583188167908321]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 44840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 44800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360588749221265395, 360588761733955624⟩, ⟨(-250224607697821677), (-249845283616912687)⟩, true⟩

def words05 : List Nat := [360583189024638938, 360583189881448811, 360583190488974592, 360583190822379800, 360583191029264511, 360583191236320388, 360583191735611913, 360583192164043499, 360583192288745803, 360583192413529934]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 44850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 44800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598823166503953, 360598835684993388⟩, ⟨(-702237988341742239), (-701858404079151415)⟩, true⟩

def words06 : List Nat := [360583192931185805, 360583193700114382, 360583194055884479, 360583194411743485, 360583194412314689, 360583194342124852, 360583193776212949, 360583193706595043, 360583193642803058, 360583193992049635]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 44860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 44800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360598518524792180, 360598531049129174⟩, ⟨(-688606597159562558), (-688226750488309496)⟩, true⟩

def words07 : List Nat := [360583194092304318, 360583194192621764, 360583194520687397, 360583195104261065, 360583195543637777, 360583195983097303, 360583196039091147, 360583196039706479, 360583196227779013, 360583196570162834]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 44870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 44800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595813560353198, 360595826090465332⟩, ⟨(-567273157091821305), (-566893051202469609)⟩, true⟩

def words08 : List Nat := [360583197193330253, 360583197321298252, 360583197321850348, 360583197199711396, 360583197077467216, 360583196746028674, 360583197079520468, 360583197494438083, 360583197596819947, 360583197878770283]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 44880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 44800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590552569730641, 360590565105649037⟩, ⟨(-331215639440317481), (-330835272879542097)⟩, true⟩

def words09 : List Nat := [360583197879279066, 360583197864685215, 360583198330178095, 360583198330792299, 360583198316575293, 360583197848188455, 360583197379706421, 360583196836870736, 360583196836128713, 360583197000865635]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 44890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 44800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 44800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk448
