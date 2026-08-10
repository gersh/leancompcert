import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk227A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360672584952362144, 360672587976992092⟩, ⟨(-2096627971640900892), (-2096581518346623522)⟩, true⟩

def state01 : KState := ⟨⟨360611502823338458, 360611505850771154⟩, ⟨(-710242373095990958), (-710195856165490076)⟩, true⟩

def words00 : List Nat := [360580234072431877, 360580234591276412, 360580236457508097, 360580238323663319, 360580239216265788, 360580239216559863, 360580238182283544, 360580235965292536, 360580233748435769, 360580234843058351]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 22700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 22700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360529314235607226, 360529317265809245⟩, ⟨1156715778739669611, 1156762358575486541⟩, true⟩

def words01 : List Nat := [360580236785173641, 360580238727173680, 360580239517434841, 360580239517729146, 360580239258196000, 360580237064701046, 360580234871310521, 360580234611048801, 360580233342734135, 360580231102014152]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 22710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 22700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360622938119475159, 360622941152460733⟩, ⟨(-970612328868584967), (-970565685776603147)⟩, true⟩

def words02 : List Nat := [360580228861425138, 360580229780235041, 360580232131314837, 360580234482246042, 360580235104101701, 360580235451088822, 360580237729214503, 360580240007225554, 360580241385953879, 360580243264740149]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 22720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 22700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360607681310154584, 360607684345943599⟩, ⟨(-623721128512334519), (-623674421684141299)⟩, true⟩

def words03 : List Nat := [360580244172060184, 360580245079332476, 360580247388861427, 360580250704710857, 360580253526253066, 360580256347600330, 360580257546005851, 360580257546300472, 360580258029790825, 360580259236155809]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 22730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 22700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360632207217909947, 360632210256479088⟩, ⟨(-1181689412730995861), (-1181642642669339211)⟩, true⟩

def words04 : List Nat := [360580262371104128, 360580264226529658, 360580264535957951, 360580264845383653, 360580264845630428, 360580265925550183, 360580267580128190, 360580269234618527, 360580269920225726, 360580272203528918]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 22740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 22700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk227A
