import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk845A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481573126303900, 362481680646898644⟩, ⟨300926515426986361, 307061213786372291⟩, true⟩

def state01 : KState := ⟨⟨362485576074736318, 362485683621822305⟩, ⟨(-37371900503289797), (-31234963500496159)⟩, true⟩

def words00 : List Nat := [371285314466627576, 371285314408182041, 371285314253704900, 371285314240843401, 371285314252741089, 371285314255680923, 371285314173743969, 371285314076489231, 371285314017641783, 371285314025396982]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 84500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 84500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477246302184130, 362477353875734401⟩, ⟨666625695466136840, 672764869103251426⟩, true⟩

def words01 : List Nat := [371285314089603830, 371285314155017337, 371285314199855651, 371285314202789924, 371285314060865787, 371285313963131264, 371285313885923728, 371285313888909306, 371285313797032294, 371285313706178122]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 84510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 84500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495471214664184, 362495578814487622⟩, ⟨(-873805231270423742), (-867663836892391080)⟩, true⟩

def words02 : List Nat := [371285313659754911, 371285313662988677, 371285313756640211, 371285313875624075, 371285313951933299, 371285313954882018, 371285313968944049, 371285314044577452, 371285314244586308, 371285314369054676]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 84520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 84500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489785146906990, 362489892773450209⟩, ⟨(-393088170966011751), (-386944517826045531)⟩, true⟩

def words03 : List Nat := [371285314487549313, 371285314607056283, 371285314865237914, 371285315062777795, 371285315253319870, 371285315444991781, 371285315631093093, 371285315655262026, 371285315711438638, 371285315769182150]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 84530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 84500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486727065410339, 362486834718115173⟩, ⟨(-134544988114618986), (-128399123138894070)⟩, true⟩

def words04 : List Nat := [371285315913504886, 371285315916441638, 371285315898862535, 371285315882236177, 371285315870239492, 371285315873584831, 371285315927453394, 371285316012948974, 371285316097405768, 371285316118416307]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 84540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 84500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk845A
