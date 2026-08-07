import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk816

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490059197797802, 362490159195883422⟩, ⟨(-409335734986976396), (-403825850161482602)⟩, true⟩

def state01 : KState := ⟨⟨362482281065258596, 362482381088490690⟩, ⟨225409626310250356, 230921563219939292⟩, true⟩

def words00 : List Nat := [371285210572505301, 371285210575330489, 371285210537581821, 371285210500556790, 371285210462475863, 371285210459231974, 371285210504213378, 371285210596579161, 371285210659921796, 371285210662847019]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 81600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 81600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501629952328876, 362501730001121367⟩, ⟨(-1353751806106270498), (-1348237783084245662)⟩, true⟩

def words01 : List Nat := [371285210745547206, 371285210864382074, 371285211030048280, 371285211083887790, 371285211112518032, 371285211142064758, 371285211264984136, 371285211320387438, 371285211524689350, 371285211730295425]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 81610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 81600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492039902474624, 362492139976752662⟩, ⟨(-571000621332251734), (-565484518049304240)⟩, true⟩

def words02 : List Nat := [371285211935055818, 371285211967235763, 371285212122967389, 371285212280192159, 371285212482838344, 371285212486302626, 371285212488465658, 371285212464681959, 371285212563011078, 371285212651128215]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 81620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 81600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485515174563167, 362485615274309436⟩, ⟨(-38323500765297452), (-32805318379522716)⟩, true⟩

def words03 : List Nat := [371285212785495708, 371285212921036573, 371285213055514985, 371285213092652239, 371285213152692582, 371285213214097259, 371285213424104453, 371285213435051294, 371285213442106768, 371285213450245798]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 81630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 81600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494730751390876, 362494830876489075⟩, ⟨(-790737117956984399), (-785216865715267081)⟩, true⟩

def words04 : List Nat := [371285213508922908, 371285213515443571, 371285213631625423, 371285213748925462, 371285213840903117, 371285213843730080, 371285213775373232, 371285213818754725, 371285214010532759, 371285214131247557]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 81640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 81600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362484495007391811, 362484595158174732⟩, ⟨45068366634247653, 50590716166889747⟩, true⟩

def words05 : List Nat := [371285214233416663, 371285214336507083, 371285214480139678, 371285214559582281, 371285214644658379, 371285214730806922, 371285214809548580, 371285214812375931, 371285214691021325, 371285214686905652]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488082408453677, 362488182584477842⟩, ⟨(-247851340985028041), (-242326930125422681)⟩, true⟩

def words06 : List Nat := [371285214808257982, 371285214843243745, 371285214866340622, 371285214890456793, 371285214959406733, 371285214973416495, 371285215136113084, 371285215299939546, 371285215434126280, 371285215473384242]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500078184296779, 362500178385903393⟩, ⟨(-1227592138939741293), (-1222065638633856447)⟩, true⟩

def words07 : List Nat := [371285215661554996, 371285215851214893, 371285216116223312, 371285216198616577, 371285216235171482, 371285216272593353, 371285216458746510, 371285216571253944, 371285216756357582, 371285216942744839]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490199395165263, 362490299622308682⟩, ⟨(-420713344669877796), (-415184758384989298)⟩, true⟩

def words08 : List Nat := [371285217121516988, 371285217124345216, 371285217143174912, 371285217186559287, 371285217238389739, 371285217241238501, 371285217188108360, 371285217135586503, 371285217176151584, 371285217241650042]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472935481213337, 362473035733791975⟩, ⟨989731037359064076, 995261701573505594⟩, true⟩

def words09 : List Nat := [371285217438558995, 371285217636603592, 371285217823673411, 371285217826502227, 371285217844845346, 371285217879421013, 371285217930823312, 371285217933652230, 371285217785507636, 371285217639563989]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk816
