import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk338A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360661346390137026, 360661353330714852⟩, ⟨(-2705156355552820740), (-2704997743153598734)⟩, true⟩

def state01 : KState := ⟨⟨360601113916237795, 360601120861124572⟩, ⟨(-669389762869213786), (-669231004806659524)⟩, true⟩

def words00 : List Nat := [360581327997479569, 360581328943665982, 360581329427575833, 360581329911585636, 360581330173308220, 360581330173760350, 360581329563714374, 360581328412246702, 360581327260760662, 360581327568858545]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 33800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 33800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360578151186631617, 360578158135774394⟩, ⟨107287379047316008, 107446281026449176⟩, true⟩

def words01 : List Nat := [360581329028494473, 360581330488130661, 360581331295905866, 360581332366327450, 360581333214746539, 360581334063235064, 360581334886534919, 360581335233013828, 360581335233416672, 360581335139944307]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 33810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 33800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360668994194652629, 360669001148063984⟩, ⟨(-2965575828212441109), (-2965416781849013583)⟩, true⟩

def words02 : List Nat := [360581335471918514, 360581336336232980, 360581337827406709, 360581339318586602, 360581339900055183, 360581340233490682, 360581341439692625, 360581342645955631, 360581344724838234, 360581347316316504]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 33820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 33800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360641040794746849, 360641047752475612⟩, ⟨(-2019773642976520172), (-2019614450533869070)⟩, true⟩

def words03 : List Nat := [360581349231299594, 360581351146207891, 360581353455587065, 360581356206275807, 360581358546326460, 360581360886315588, 360581362786793373, 360581364709814317, 360581366473866013, 360581368237965584]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 33830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 33800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588994241246657, 360589001203232134⟩, ⟨(-258283417057205406), (-258124080545309664)⟩, true⟩

def words04 : List Nat := [360581370542941251, 360581371978033173, 360581372874392499, 360581373770748038, 360581374060877593, 360581374791804778, 360581375232124995, 360581375672502438, 360581375676011427, 360581375901747827]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 33840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 33800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk338A
