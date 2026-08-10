import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk998A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584465534823415, 360584531530730529⟩, ⟨(-213668528777273346), (-209221249785728006)⟩, true⟩

def state01 : KState := ⟨⟨360576793514411182, 360576859524151079⟩, ⟨551917303265649266, 556365962838017046⟩, true⟩

def words00 : List Nat := [360582435147739361, 360582435105699527, 360582434984449735, 360582434848621245, 360582434712410432, 360582434551049314, 360582434391714277, 360582434152663814, 360582433913339791, 360582433774855799]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577002536561193, 360577068559992077⟩, ⟨531088129017645950, 535538155155140126⟩, true⟩

def words01 : List Nat := [360582433746581314, 360582433774432704, 360582433775749046, 360582433718370581, 360582433695802340, 360582433648220554, 360582433651352569, 360582433652805715, 360582433650828169, 360582433598613147]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602183973411150, 360602250010543388⟩, ⟨(-1982634540698770606), (-1978183146826962188)⟩, true⟩

def words02 : List Nat := [360582433574686890, 360582433663418905, 360582433852029597, 360582434040918927, 360582434130929749, 360582434226393558, 360582434281097697, 360582434336216933, 360582434491191343, 360582434691185404]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360604736307709757, 360604802358662742⟩, ⟨(-2237442509209058446), (-2232989735540840006)⟩, true⟩

def words03 : List Nat := [360582434835812088, 360582434980594483, 360582435225389675, 360582435548243741, 360582435823531610, 360582436099060452, 360582436324173375, 360582436449359767, 360582436674550908, 360582436900228424]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580600641900625, 360580666706546216⟩, ⟨172327596049042617, 176781736854576977⟩, true⟩

def words04 : List Nat := [360582437082283054, 360582437164524214, 360582437182026618, 360582437199685601, 360582437200903395, 360582437200596533, 360582437210947339, 360582437221592798, 360582437222886625, 360582437179624380]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk998A
