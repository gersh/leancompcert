import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk169A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360535586174020702, 360535587806608197⟩, ⟨799810767153150605, 799829444868970639⟩, true⟩

def state01 : KState := ⟨⟨360635023446124024, 360635025080727391⟩, ⟨(-880948219960677500), (-880929508166796748)⟩, true⟩

def words00 : List Nat := [360582912880098672, 360582915376612468, 360582921359773624, 360582927342267650, 360582929871083134, 360582930189286014, 360582930189460367, 360582929457086531, 360582929899656174, 360582932980427776]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 16900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 16900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577649456206935, 360577651092850275⟩, ⟨89566686873641772, 89585433173780384⟩, true⟩

def words01 : List Nat := [360582934307685730, 360582935634812011, 360582937953839879, 360582942013819646, 360582944022864261, 360582946031705726, 360582946275081835, 360582946275297159, 360582946052896196, 360582945740200972]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 16910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 16900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360605951286808018, 360605952925466375⟩, ⟨(-389490110217788388), (-389471329813557068)⟩, true⟩

def words02 : List Nat := [360582948593836553, 360582948594050518, 360582948299326994, 360582946241907429, 360582944184696401, 360582941239153836, 360582944356141674, 360582947652819669, 360582948121357581, 360582949480317621]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 16920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 16900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360636751971544305, 360636753612226075⟩, ⟨(-911251130355041490), (-911232315684416184)⟩, true⟩

def words03 : List Nat := [360582954314708942, 360582959148592161, 360582962443657069, 360582962443871181, 360582962282913248, 360582959196549252, 360582956498851709, 360582958682036842, 360582961857826685, 360582965033294229]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 16930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 16900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360607733046252000, 360607734688970194⟩, ⟨(-419824687855762731), (-419805838677871473)⟩, true⟩

def words04 : List Nat := [360582966448648016, 360582966448862310, 360582968722935460, 360582971595544153, 360582973556929340, 360582973791386254, 360582973791582067, 360582971288316586, 360582968785305693, 360582968843965306]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 16940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 16900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk169A
