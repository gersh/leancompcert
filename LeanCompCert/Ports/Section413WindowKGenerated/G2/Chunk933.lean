import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk933

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582974367106601, 360583031746654730⟩, ⟨(-95722685995129322), (-92107652820280530)⟩, true⟩

def state01 : KState := ⟨⟨360591904297169030, 360591961689450196⟩, ⟨(-928985210842153690), (-925368989610626460)⟩, true⟩

def words00 : List Nat := [360582044582808701, 360582044611041473, 360582044612277036, 360582044550816456, 360582044489136746, 360582044398892325, 360582044445944853, 360582044527679524, 360582044540993458, 360582044648698188]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360603090654170396, 360603148059195633⟩, ⟨(-1972887308837187467), (-1969269898392228551)⟩, true⟩

def words01 : List Nat := [360582044810356491, 360582044972421992, 360582045098197920, 360582045243208757, 360582045290613560, 360582045338123024, 360582045382776807, 360582045495615059, 360582045722838060, 360582045950362764]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360603959465433930, 360604016883339845⟩, ⟨(-2054059807686823826), (-2050441195156377496)⟩, true⟩

def words02 : List Nat := [360582046120661721, 360582046228917839, 360582046451688160, 360582046674886790, 360582046868509140, 360582046947827470, 360582046955066922, 360582046962450917, 360582047084338953, 360582047321295547]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591564929609099, 360591622360249239⟩, ⟨(-897251471218506634), (-893631670138602672)⟩, true⟩

def words03 : List Nat := [360582047533268677, 360582047745477001, 360582047890354800, 360582047982363946, 360582048000319878, 360582048018626085, 360582048151289738, 360582048313871938, 360582048417659658, 360582048521634498]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360612153998078250, 360612211441465243⟩, ⟨(-2819123087987366981), (-2815502097053776157)⟩, true⟩

def words04 : List Nat := [360582048695197739, 360582048937492776, 360582049272066953, 360582049606893001, 360582049831910774, 360582050039093045, 360582050238306892, 360582050437921992, 360582050732008580, 360582051056498250]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360586061220596283, 360586118676861672⟩, ⟨(-383207560464012058), (-379585367267825398)⟩, true⟩

def words05 : List Nat := [360582051295899669, 360582051535465380, 360582051772165228, 360582052066517937, 360582052331584142, 360582052596865210, 360582052758713994, 360582052806244677, 360582052850906389, 360582052895997416]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587857952269115, 360587915421264981⟩, ⟨(-550987264154225690), (-547363882380027306)⟩, true⟩

def words06 : List Nat := [360582053028628905, 360582053047081113, 360582053048284872, 360582053009068077, 360582052969628135, 360582052889416114, 360582052982002220, 360582053074854463, 360582053109890828, 360582053174074954]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591818995888619, 360591876477655105⟩, ⟨(-920844790641046247), (-917220216412916673)⟩, true⟩

def words07 : List Nat := [360582053352608840, 360582053531537044, 360582053707475938, 360582053769244223, 360582053770503892, 360582053735740353, 360582053779248432, 360582053921696688, 360582054027990836, 360582054134604454]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581350682727742, 360581408177357383⟩, ⟨56640686230378627, 60266461684045845⟩, true⟩

def words08 : List Nat := [360582054161490222, 360582054162841780, 360582054101135409, 360582054128557290, 360582054129690769, 360582054103071279, 360582053998401395, 360582053805672969, 360582053612689220, 360582053497645252]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584059968290045, 360584117475639239⟩, ⟨(-196368902125654805), (-192741938729450859)⟩, true⟩

def words09 : List Nat := [360582053566017089, 360582053641562627, 360582053659474620, 360582053682635565, 360582053683766723, 360582053678137267, 360582053742882948, 360582053832751482, 360582053856050417, 360582053879545735]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk933
