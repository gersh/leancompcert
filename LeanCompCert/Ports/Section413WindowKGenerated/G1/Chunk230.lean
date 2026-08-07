import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk230

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490386737543651, 362490393905486113⟩, ⟨(-143353427352361652), (-143241949504773540)⟩, true⟩

def state01 : KState := ⟨⟨362443296142145466, 362443303316605802⟩, ⟨939958158248696115, 940069786040162155⟩, true⟩

def words00 : List Nat := [371284166265949821, 371284165826272227, 371284164380985181, 371284164603577463, 371284165229616939, 371284165230338226, 371284163340403477, 371284161446928302, 371284159553325294, 371284158153026496]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 23000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 23000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362449748885298150, 362449756066245635⟩, ⟨791617880315991729, 791729657410580375⟩, true⟩

def words01 : List Nat := [371284156490853552, 371284156604409703, 371284156719124183, 371284156719846292, 371284154682728180, 371284153216235844, 371284152169584913, 371284152170308684, 371284150681082138, 371284149187766512]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 23010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 23000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487010319436811, 362487017506855967⟩, ⟨(-66361724670185127), (-66249798564735119)⟩, true⟩

def words02 : List Nat := [371284148087124987, 371284148087927327, 371284147542972990, 371284146870028582, 371284146196910280, 371284145219257883, 371284142236427773, 371284141140108454, 371284140832254065, 371284140957919111]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 23020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 23000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488793845301042, 362488801039312728⟩, ⟨(-107374947827940742), (-107262869863705958)⟩, true⟩

def words03 : List Nat := [371284141063141526, 371284141168598337, 371284142836447132, 371284143847310684, 371284145015121297, 371284146183101773, 371284147010829104, 371284147011551646, 371284145531895821, 371284145734861372]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 23030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 23000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472013078857573, 362472020279302917⟩, ⟨279450398624873992, 279562624854299392⟩, true⟩

def words04 : List Nat := [371284147821366362, 371284147822089276, 371284147779252990, 371284147732224127, 371284147691133575, 371284147691930688, 371284147547830899, 371284148158916625, 371284148808916488, 371284148809665360]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 23040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 23000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362531966582189304, 362531973789172330⟩, ⟨(-1102923121716764768), (-1102810744760925504)⟩, true⟩

def words05 : List Nat := [371284148284004575, 371284148197640863, 371284149905904133, 371284149906627230, 371284149195861097, 371284148165103447, 371284147984248672, 371284148177712776, 371284150252168123, 371284152326756957]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 23050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 23000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486057382611458, 362486064596113625⟩, ⟨(-44001438760795295), (-43888911439804937)⟩, true⟩

def words06 : List Nat := [371284154397623816, 371284154680336194, 371284156843612961, 371284159007081967, 371284161293482219, 371284161661594274, 371284161662144257, 371284161639041755, 371284162171732967, 371284162255017019]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 23060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 23000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472946216812915, 362472953436847800⟩, ⟨258745066470545183, 258857744534654981⟩, true⟩

def words07 : List Nat := [371284164217942727, 371284166181015105, 371284168140874553, 371284168141598448, 371284167955449762, 371284168014129415, 371284169639509947, 371284169640238643, 371284169595504617, 371284169110354501]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 23070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 23000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362532573052220565, 362532580278738054⟩, ⟨(-1117578989763980406), (-1117466162048718970)⟩, true⟩

def words08 : List Nat := [371284170017475564, 371284170474785858, 371284172298500143, 371284174122343642, 371284175752947132, 371284176211252057, 371284178546731743, 371284180882396550, 371284184168761735, 371284186265397414]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 23080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 23000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362521630339358179, 362521637572473666⟩, ⟨(-864850444525231735), (-864737464429186949)⟩, true⟩

def words09 : List Nat := [371284188291675824, 371284190318016639, 371284193097506324, 371284194947612290, 371284197193579401, 371284199439634227, 371284201682366365, 371284201683090890, 371284203049294241, 371284204670675944]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 23090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 23000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 23000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk230
