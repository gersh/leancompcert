import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk780A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360596324209786191, 360596363759171521⟩, ⟨(-1105026184650428170), (-1102942677796248810)⟩, true⟩

def state01 : KState := ⟨⟨360590585719873874, 360590625279753361⟩, ⟨(-657497936545519243), (-655413611094020513)⟩, true⟩

def words00 : List Nat := [360582223745489001, 360582223746603240, 360582223740194210, 360582223646670274, 360582223552967263, 360582223418432769, 360582223476163893, 360582223587766085, 360582223617131586, 360582223725984098]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 78000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 78000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360609332724297644, 360609372294693768⟩, ⟨(-2120095301999127974), (-2118010156092959944)⟩, true⟩

def words01 : List Nat := [360582223970430869, 360582224215218082, 360582224427117399, 360582224568842113, 360582224569887626, 360582224557445519, 360582224695298417, 360582224929098149, 360582225277953047, 360582225627051814]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 78010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 78000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595348927521271, 360595388508553604⟩, ⟨(-1029070588003171034), (-1026984612208416358)⟩, true⟩

def words02 : List Nat := [360582225892837604, 360582226162957841, 360582226400622491, 360582226638601506, 360582226833615599, 360582226980229904, 360582227034351391, 360582227088592086, 360582227099958503, 360582227269915007]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 78020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 78000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360580253073070981, 360580292664596387⟩, ⟨149024972009827210, 151111766631924982⟩, true⟩

def words03 : List Nat := [360582227603499393, 360582227937288549, 360582228152527830, 360582228343289014, 360582228492763433, 360582228642550609, 360582228915358770, 360582229024593799, 360582229025603211, 360582229001944311]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 78030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 78000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360600009425981868, 360600049028036467⟩, ⟨(-1392885125165726196), (-1390797508792826736)⟩, true⟩

def words04 : List Nat := [360582229117195682, 360582229339561787, 360582229557734944, 360582229776100213, 360582229828105328, 360582229829219698, 360582229717343749, 360582229661510568, 360582229712206796, 360582229941685328]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 78040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 78000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk780A
