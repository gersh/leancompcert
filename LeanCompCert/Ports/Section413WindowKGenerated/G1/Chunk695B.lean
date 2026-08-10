import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk695A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk695B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk695A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk695B
