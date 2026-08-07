import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk360

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473350931059208, 362473369163496633⟩, ⟨417975384199469459, 418418972688395369⟩, true⟩

def state01 : KState := ⟨⟨362454705710924831, 362454723953801796⟩, ⟨1089235425816263159, 1089679390183367679⟩, true⟩

def words00 : List Nat := [371284991590701733, 371284991469098260, 371284990469854324, 371284989332631796, 371284988195036992, 371284987229171195, 371284985948175935, 371284985438534301, 371284984928501886, 371284984420066261]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 36000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 36000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362523177170505390, 362523195423949880⟩, ⟨(-1376754774472730024), (-1376310429514703468)⟩, true⟩

def words01 : List Nat := [371284983580549614, 371284983512296400, 371284984144402064, 371284984160714918, 371284984161637365, 371284983987253492, 371284984407216845, 371284984743332881, 371284985804946507, 371284986867010465]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 36010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 36000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482886255541315, 362482904519562319⟩, ⟨74716579968733302, 75161305947244146⟩, true⟩

def words02 : List Nat := [371284987926588632, 371284988478592840, 371284989307947386, 371284990137869046, 371284990985525734, 371284990986697671, 371284990807927151, 371284990630886468, 371284990593884264, 371284990595220028]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 36020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 36000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477696164350792, 362477714438946086⟩, ⟨261853349540558196, 262298456561330800⟩, true⟩

def words03 : List Nat := [371284991153374388, 371284991769883883, 371284992384124672, 371284992385297325, 371284992113219705, 371284992076114095, 371284992769260806, 371284992770433719, 371284992621154358, 371284992420537688]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 36030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 36000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362462577979155333, 362462596264256745⟩, ⟨806864168722795395, 807309654437743715⟩, true⟩

def words04 : List Nat := [371284992564595669, 371284992565886874, 371284992688305563, 371284992849119204, 371284992869403319, 371284992870576074, 371284991993708515, 371284991363016629, 371284990731742317, 371284990429428389]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 36040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 36000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362470350872482627, 362470369168239165⟩, ⟨526636314739399344, 527082184627297078⟩, true⟩

def words05 : List Nat := [371284989809125224, 371284989170825011, 371284988534050101, 371284988535353640, 371284988154375081, 371284988007889717, 371284987861024458, 371284987455860048, 371284986382603668, 371284985978683627]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 36050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 36000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479731115542262, 362479749421747670⟩, ⟨188460100905468917, 188906347632939233⟩, true⟩

def words06 : List Nat := [371284985937354040, 371284985938535339, 371284985798161180, 371284985659715225, 371284985615182417, 371284985616474498, 371284985809247122, 371284986290614665, 371284986635604899, 371284986636819280]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 36060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 36000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362523163165779055, 362523181482624323⟩, ⟨(-1378392115905431664), (-1377945485346450870)⟩, true⟩

def words07 : List Nat := [371284986665414115, 371284986839808543, 371284987781636139, 371284987941397373, 371284987968550597, 371284987996052089, 371284988652399001, 371284989028217532, 371284990087563370, 371284991147396740]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 36070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 36000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492138865876377, 362492157193300698⟩, ⟨(-258961331933170677), (-258514319627306079)⟩, true⟩

def words08 : List Nat := [371284992173406869, 371284992176472527, 371284992946747979, 371284993717575905, 371284994524075675, 371284994525249628, 371284994308748810, 371284994034187017, 371284994146241522, 371284994346063789]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 36080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 36000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362454556796307374, 362454575134305022⟩, ⟨1097625692015626342, 1098073085965852796⟩, true⟩

def words09 : List Nat := [371284994738411880, 371284995131218769, 371284995472317748, 371284995473491945, 371284994791938702, 371284994344503880, 371284994214691836, 371284994215866103, 371284993512615089, 371284992671312387]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 36090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 36000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 36000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk360
