import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk828A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360595165081715776, 360595209856420023⟩, ⟨(-1063844091854522969), (-1061340335689262683)⟩, true⟩

def state01 : KState := ⟨⟨360600870691489868, 360600915477394635⟩, ⟨(-1536344931899991585), (-1533840248276652019)⟩, true⟩

def words00 : List Nat := [360582392134636092, 360582392315161006, 360582392383864461, 360582392452677436, 360582392484653866, 360582392613518614, 360582392790800126, 360582392968310353, 360582393072463321, 360582393297391053]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360615554434916936, 360615599232015295⟩, ⟨(-2752344446196749218), (-2749838835575474164)⟩, true⟩

def words01 : List Nat := [360582393667790879, 360582394038530778, 360582394554683805, 360582394973839414, 360582395268834688, 360582395563915170, 360582395854818377, 360582396234907415, 360582396636779405, 360582397038905149]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595097794402525, 360595142602813641⟩, ⟨(-1058168720307760460), (-1055662172708920492)⟩, true⟩

def words02 : List Nat := [360582397351505159, 360582397518791038, 360582397665996280, 360582397813568317, 360582397922393924, 360582397923581541, 360582397887050671, 360582397777518069, 360582397676027555, 360582397831258198]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585541439206637, 360585586258812045⟩, ⟨(-266599588528618976), (-264092113651817890)⟩, true⟩

def words03 : List Nat := [360582397982165473, 360582398133280927, 360582398211109650, 360582398212297504, 360582398179546266, 360582398110511143, 360582398116427598, 360582398239842430, 360582398279384962, 360582398319100407]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596422660598583, 360596467491411523⟩, ⟨(-1168086609515518473), (-1165578206150590193)⟩, true⟩

def words04 : List Nat := [360582398320069783, 360582398380433129, 360582398531430509, 360582398682651487, 360582398695119615, 360582398696309247, 360582398729910196, 360582398820363277, 360582398954197821, 360582399125234283]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk828A
