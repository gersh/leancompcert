import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk897A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582924555178673, 360582977429835727⟩, ⟨(-87616002983126402), (-84413225064505992)⟩, true⟩

def state01 : KState := ⟨⟨360574689842642198, 360574742729468620⟩, ⟨651062464353577078, 654266333927894602⟩, true⟩

def words00 : List Nat := [360582036491524827, 360582036492818791, 360582036481600631, 360582036408798830, 360582036335813869, 360582036146717487, 360582036019540582, 360582035993356314, 360582035967034103, 360582035855473836]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 89700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 89700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582728884184627, 360582781783245664⟩, ⟨(-70165681332600728), (-66960714130936398)⟩, true⟩

def words01 : List Nat := [360582035800760622, 360582035827761415, 360582035851004088, 360582035852299295, 360582035802572460, 360582035647583738, 360582035492341732, 360582035442672636, 360582035452055897, 360582035461714129]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 89710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 89700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581125651683679, 360581178563084520⟩, ⟨73564656554797250, 76770730942377198⟩, true⟩

def words02 : List Nat := [360582035462879175, 360582035408851352, 360582035256323371, 360582035116070842, 360582034975479945, 360582034764102048, 360582034655802378, 360582034454266339, 360582034252486884, 360582034137930641]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 89720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 89700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360560072407279104, 360560125330884625⟩, ⟨1962806347249773540, 1966013516825507152⟩, true⟩

def words03 : List Nat := [360582034207203378, 360582034286257275, 360582034287430655, 360582034271550263, 360582034131435410, 360582033940627914, 360582033749446568, 360582033613186557, 360582033457724252, 360582033214958901]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 89730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 89700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360563470469458140, 360563523405276261⟩, ⟨1657895513680284702, 1661103779275712984⟩, true⟩

def words04 : List Nat := [360582032971882255, 360582032808662678, 360582032707289131, 360582032648007115, 360582032588626470, 360582032427304849, 360582032208786992, 360582031987714967, 360582031766260190, 360582031525379612]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 89740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 89700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk897A
