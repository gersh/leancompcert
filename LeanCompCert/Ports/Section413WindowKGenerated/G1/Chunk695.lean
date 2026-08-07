import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk695

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362503012356938866, 362503084001411913⟩, ⟨(-1233176041546534961), (-1229813185494441971)⟩, true⟩

def state01 : KState := ⟨⟨362488299322190619, 362488370988136555⟩, ⟨(-210559827965084525), (-207195479437659873)⟩, true⟩

def words00 : List Nat := [371285389359171614, 371285389448998920, 371285389625380857, 371285389802997814, 371285390042821107, 371285390059772234, 371285390075843078, 371285390092678544, 371285390184348931, 371285390229991260]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 69500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 69500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362467219077462106, 362467290764831968⟩, ⟨1254890367065093742, 1258256204879547530⟩, true⟩

def words01 : List Nat := [371285390411320201, 371285390593625433, 371285390734911116, 371285390737289706, 371285390602860226, 371285390533036408, 371285390476646341, 371285390479025004, 371285390219881586, 371285389962255437]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 69510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 69500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476962175399878, 362477033884046016⟩, ⟨577528509243221049, 580895826294663417⟩, true⟩

def words02 : List Nat := [371285389703530757, 371285389598479597, 371285389388804156, 371285389341872432, 371285389294186954, 371285389210424842, 371285388850415863, 371285388681591478, 371285388511520012, 371285388491068808]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 69520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 69500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482870128340784, 362482941858666862⟩, ⟨166691069195502701, 170059893761752585⟩, true⟩

def words03 : List Nat := [371285388372735050, 371285388175776491, 371285387977878159, 371285387953220189, 371285387824366898, 371285387759937394, 371285387694679371, 371285387628250011, 371285387388372748, 371285387356132519]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 69530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 69500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482708878944889, 362482780630440735⟩, ⟨177953448002330608, 181323744825293280⟩, true⟩

def words04 : List Nat := [371285387480658497, 371285387504938938, 371285387528344106, 371285387552557022, 371285387583092886, 371285387585715633, 371285387600593431, 371285387675783015, 371285387727097171, 371285387729575535]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 69540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 69500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362494667343171506, 362494739116234872⟩, ⟨(-653790524941517914), (-650418727995674192)⟩, true⟩

def words05 : List Nat := [371285387846295044, 371285388001845312, 371285388263362048, 371285388277394314, 371285388279235738, 371285388259801288, 371285388423628720, 371285388506965641, 371285388643036728, 371285388780155810]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 69550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 69500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485467346636768, 362485539141195380⟩, ⟨(-13858778962569269), (-10485486699056587)⟩, true⟩

def words06 : List Nat := [371285388898901455, 371285388901281737, 371285388744658962, 371285388725965893, 371285388747936947, 371285388750359075, 371285388621518720, 371285388494087222, 371285388419945271, 371285388424852378]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 69560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 69500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362471311719444569, 362471383535442789⟩, ⟨971060679224161232, 974435463149730060⟩, true⟩

def words07 : List Nat := [371285388584184560, 371285388744458317, 371285388860686463, 371285388863068167, 371285388737421033, 371285388594842224, 371285388464323770, 371285388466709765, 371285388267837866, 371285388069262130]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 69570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 69500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474344854880488, 362474416692171313⟩, ⟨760059969307245894, 763436234884698014⟩, true⟩

def words08 : List Nat := [371285387869611627, 371285387802949900, 371285387644290211, 371285387659355957, 371285387661198052, 371285387642535145, 371285387437606062, 371285387320938886, 371285387203048381, 371285387179811559]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 69580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 69500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485433140605502, 362485504999615199⟩, ⟨(-11617840279193859), (-8240063181338303)⟩, true⟩

def words09 : List Nat := [371285387023948933, 371285386869461502, 371285386762884365, 371285386765554186, 371285386772340451, 371285386804650274, 371285386806463958, 371285386784427980, 371285386604910857, 371285386609603830]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 69590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 69500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 69500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk695
