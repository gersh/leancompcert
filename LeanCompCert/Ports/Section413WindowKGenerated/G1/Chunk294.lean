import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk294

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493006278967322, 362493018235534683⟩, ⟨(-220859411473562690), (-220621796244785554)⟩, true⟩

def state01 : KState := ⟨⟨362479487560132543, 362479499525077640⟩, ⟨176719568068052992, 176957429646122282⟩, true⟩

def words00 : List Nat := [371285515760083704, 371285515810664304, 371285515811380512, 371285515640877711, 371285515651165446, 371285515652207852, 371285515802946971, 371285516118911808, 371285516437723847, 371285516438700426]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 29400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 29400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362540923654241551, 362540935627686006⟩, ⟨(-1630316218372359599), (-1630078106784901313)⟩, true⟩

def words01 : List Nat := [371285517185490710, 371285518137285512, 371285520065450955, 371285521367260020, 371285522412762483, 371285523458493724, 371285525318905962, 371285526600984080, 371285528485006905, 371285530369306451]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 29410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 29400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362507506408352765, 362507518390312023⟩, ⟨(-647126635421517393), (-646888273285269707)⟩, true⟩

def words02 : List Nat := [371285532057434714, 371285532437860581, 371285533972311384, 371285535507156496, 371285537069238800, 371285537093776767, 371285537094483497, 371285536950761943, 371285537815891232, 371285538563826846]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 29420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 29400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480301735768573, 362480313726215493⟩, ⟨153747136425966201, 153985748396919419⟩, true⟩

def words03 : List Nat := [371285540152593015, 371285541741644722, 371285543333654119, 371285543388915067, 371285543394542320, 371285543400618449, 371285544559440555, 371285544560383184, 371285544396986148, 371285544220386585]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 29430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 29400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362496840980737647, 362496852979633812⟩, ⟨(-333078232397870453), (-332839371638086853)⟩, true⟩

def words04 : List Nat := [371285544803260805, 371285545158025591, 371285546665128655, 371285548172505588, 371285549553254061, 371285549554196665, 371285549826654149, 371285550255310237, 371285551132418886, 371285551517149072]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 29440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 29400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362529493268067568, 362529505275540443⟩, ⟨(-1294856280519522713), (-1294617167131341521)⟩, true⟩

def words05 : List Nat := [371285551905380782, 371285552293895242, 371285553833855137, 371285554796765716, 371285555978284623, 371285557160112807, 371285558352615012, 371285558867989199, 371285560360361140, 371285561853147064]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 29450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 29400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497791433712232, 362497803449594554⟩, ⟨(-360770465639050273), (-360531104464968455)⟩, true⟩

def words06 : List Nat := [371285564075012423, 371285564763140234, 371285565183417161, 371285565603978739, 371285566302557736, 371285566434172797, 371285567575879046, 371285568717881910, 371285569614042062, 371285570030149508]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 29460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 29400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362528374868033360, 362528386892449381⟩, ⟨(-1262194544496936427), (-1261954931791383547)⟩, true⟩

def words07 : List Nat := [371285571197333834, 371285572364936497, 371285574681954041, 371285575466548945, 371285576049864821, 371285576633417809, 371285577695776595, 371285578283528366, 371285579736293383, 371285581189393468]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 29470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 29400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362509479387185509, 362509491420117963⟩, ⟨(-705153278937139862), (-704913415124852392)⟩, true⟩

def words08 : List Nat := [371285582659022380, 371285582659966170, 371285583684001402, 371285584771331513, 371285586210063548, 371285586420886860, 371285586635863645, 371285586851157755, 371285587946165712, 371285588757776068]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 29480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 29400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362465457325599876, 362465469367029959⟩, ⟨593274586315875100, 593514700767001742⟩, true⟩

def words09 : List Nat := [371285589688567374, 371285590619654471, 371285591507204925, 371285591508149134, 371285590865198569, 371285590285477637, 371285589875802988, 371285589876764166, 371285589190404360, 371285588509428841]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 29490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 29400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 29400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk294
