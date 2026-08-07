import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk459

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493160531591558, 362493190763073655⟩, ⟨(-352502190598578845), (-351564658484172557)⟩, true⟩

def state01 : KState := ⟨⟨362484516777776924, 362484547022812210⟩, ⟨44327996040239291, 45266150316535853⟩, true⟩

def words00 : List Nat := [371285532174074870, 371285532211848146, 371285532212999429, 371285532168785231, 371285532222089096, 371285532223794603, 371285532432774090, 371285532715538606, 371285532997066008, 371285532998641366]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 45900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 45900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362504392096606321, 362504422355441927⟩, ⟨(-868235813279447732), (-867297025361881490)⟩, true⟩

def words01 : List Nat := [371285533349117369, 371285533721852564, 371285534282283339, 371285534417815161, 371285534478411495, 371285534539472170, 371285534792915899, 371285534810988951, 371285535223336755, 371285535636394827]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 45910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 45900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467293960941158, 362467324233489276⟩, ⟨835448759143827767, 836388176811910447⟩, true⟩

def words02 : List Nat := [371285536048868167, 371285536050390515, 371285535962234846, 371285536095113309, 371285536233300013, 371285536234822514, 371285535741631063, 371285535156114572, 371285534569997001, 371285534296123980]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 45920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 45900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466580415387530, 362466610701636494⟩, ⟨868310703214649660, 869250750231056568⟩, true⟩

def words03 : List Nat := [371285533900693467, 371285533840700812, 371285533780211727, 371285533685818288, 371285533292052962, 371285533043124572, 371285532956816009, 371285532958339118, 371285532547395486, 371285532137209656]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 45930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 45900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478600516961383, 362478630816857778⟩, ⟨316098040692207319, 317038714742078959⟩, true⟩

def words04 : List Nat := [371285531726397709, 371285531513782769, 371285531318950928, 371285531459216108, 371285531522574697, 371285531524098123, 371285530956439608, 371285530634472081, 371285530460866404, 371285530462445201]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 45940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 45900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490201154374453, 362490231468162582⟩, ⟨(-217014380230367681), (-216073067785301271)⟩, true⟩

def words05 : List Nat := [371285530313435743, 371285530105666093, 371285530160703871, 371285530236931190, 371285530292060386, 371285530347731976, 371285530403151637, 371285530404685624, 371285530137546787, 371285530241736149]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 45950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 45900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475309047947271, 362475339375330246⟩, ⟨467552301337889864, 468494238671702888⟩, true⟩

def words06 : List Nat := [371285530531460273, 371285530533011219, 371285530464333790, 371285530395182786, 371285530341084964, 371285530342764400, 371285530380472437, 371285530596968012, 371285530677617561, 371285530679195195]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 45960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 45900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362512596830501292, 362512627171643024⟩, ⟨(-1246745630663533486), (-1245803060769730192)⟩, true⟩

def words07 : List Nat := [371285530709383055, 371285530962038218, 371285531605665343, 371285531680722881, 371285531681904354, 371285531679037680, 371285532005563910, 371285532124184410, 371285532714498268, 371285533305464174]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 45970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 45900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485656849867183, 362485687204789329⟩, ⟨(-8009737347985684), (-7066533761313404)⟩, true⟩

def words08 : List Nat := [371285533883543407, 371285533903198691, 371285534119834278, 371285534337252814, 371285534588633935, 371285534590158615, 371285534211815849, 371285533834329625, 371285533549301975, 371285533554428143]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 45980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 45900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362466905882967000, 362466936251622201⟩, ⟨854517639656829784, 855461474896561700⟩, true⟩

def words09 : List Nat := [371285533719936196, 371285533886061898, 371285534052048224, 371285534053581969, 371285533889966852, 371285533870799751, 371285534027399963, 371285534028925140, 371285533642760697, 371285533240206909]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 45990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 45900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 45900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk459
