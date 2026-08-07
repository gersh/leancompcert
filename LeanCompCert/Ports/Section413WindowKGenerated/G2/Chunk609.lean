import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk609

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602494544759892, 360602518184756856⟩, ⟨(-1224575536257857692), (-1223602948958935256)⟩, true⟩

def state01 : KState := ⟨⟨360583910103136060, 360583933751155674⟩, ⟨(-92647553617970822), (-91674477698746652)⟩, true⟩

def words00 : List Nat := [360582427112366484, 360582427562262447, 360582427834839363, 360582428107494586, 360582428231676844, 360582428490458340, 360582428601175404, 360582428712035395, 360582428712795194, 360582428694963874]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 60900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 60900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360644962544369215, 360644986200442945⟩, ⟨(-3811737039758357571), (-3810763473224481633)⟩, true⟩

def words01 : List Nat := [360582428811088953, 360582428927468745, 360582429313044051, 360582429801916456, 360582430059431613, 360582430317004480, 360582430843833095, 360582431602221795, 360582432629743270, 360582433657424537]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 60910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 60900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360622417968583227, 360622441632797251⟩, ⟨(-2438287721429356830), (-2437313658948331568)⟩, true⟩

def words02 : List Nat := [360582434474099952, 360582435092170502, 360582435979449534, 360582436866949943, 360582437686217350, 360582438349495145, 360582438841936782, 360582439334471706, 360582439766413011, 360582440423906074]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 60920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 60900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573473516357320, 360573497188601283⟩, ⟨544168141709947777, 545142693496168907⟩, true⟩

def words03 : List Nat := [360582441079242830, 360582441734718153, 360582442228794715, 360582442454698910, 360582442497884286, 360582442541282151, 360582442853740434, 360582442898121754, 360582442898890261, 360582442752984220]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 60930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 60900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610189822030992, 360610213502340135⟩, ⟨(-1693445922870160063), (-1692470879552546067)⟩, true⟩

def words04 : List Nat := [360582442668422674, 360582442941397190, 360582443483355336, 360582444025463426, 360582444303262687, 360582444422675121, 360582444723034133, 360582445023642513, 360582445316391622, 360582445772859856]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 60940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 60900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360607587459227151, 360607611147661382⟩, ⟨(-1534825277774783642), (-1533849739192059052)⟩, true⟩

def words05 : List Nat := [360582446024810941, 360582446276843862, 360582446797867395, 360582447453196823, 360582448001370664, 360582448549680962, 360582448924814011, 360582449156148484, 360582449569601157, 360582449983323657]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 60950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 60900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360634795969652009, 360634819666140013⟩, ⟨(-3193599255720449438), (-3192623226139971888)⟩, true⟩

def words06 : List Nat := [360582450665850145, 360582451453471459, 360582452035679710, 360582452617949064, 360582453085649006, 360582453686836184, 360582454445220630, 360582455203743648, 360582455826854500, 360582456686590064]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 60900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360622305877211448, 360622329581753581⟩, ⟨(-2432040124466581075), (-2431063603785831625)⟩, true⟩

def words07 : List Nat := [360582457662254961, 360582458638137112, 360582459549025859, 360582460292678466, 360582460806265978, 360582461319895631, 360582461769737116, 360582462353692860, 360582463008160600, 360582463662798729]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 60970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 60900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596931474562505, 360596955187238217⟩, ⟨(-884731889484135392), (-883754872778270176)⟩, true⟩

def words08 : List Nat := [360582464182072708, 360582464433624842, 360582464764039150, 360582465094721817, 360582465356326411, 360582465357180677, 360582465351042730, 360582465179494625, 360582465026026087, 360582465264581133]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 60980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 60900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360566222224590070, 360566245945322044⟩, ⟨988348153434809820, 989325661531329580⟩, true⟩

def words09 : List Nat := [360582465495228247, 360582465726019648, 360582465813770140, 360582465814624546, 360582465634605216, 360582465282526846, 360582464930200919, 360582464793795467, 360582464663784741, 360582464398789771]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 60990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 60900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 60900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk609
