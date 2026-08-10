import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk383A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360647444943150271, 360647453946772905⟩, ⟨(-2508421962385351499), (-2508188873450607927)⟩, true⟩

def state01 : KState := ⟨⟨360644163255248253, 360644172263794834⟩, ⟨(-2382872919558583767), (-2382639642012211469)⟩, true⟩

def words00 : List Nat := [360581968931032064, 360581970062920905, 360581971874717976, 360581973686588217, 360581975197284297, 360581976212054048, 360581976882334342, 360581977552636325, 360581978589438272, 360581980213417339]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360600155928879513, 360600164942304649⟩, ⟨(-696887364337564195), (-696653899869945713)⟩, true⟩

def words01 : List Nat := [360581981540907957, 360581982868419156, 360581983631360091, 360581983717425874, 360581983717858967, 360581983483065797, 360581983692454742, 360581984563430998, 360581985038327783, 360581985513274354]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360659022536649697, 360659031554957734⟩, ⟨(-2952947051969024553), (-2952713400364314109)⟩, true⟩

def words02 : List Nat := [360581986667659523, 360581988168192299, 360581989961382781, 360581991754583850, 360581992911450193, 360581993391756693, 360581994551308582, 360581995710951470, 360581997549716505, 360581999559957231]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360627627005276548, 360627636028524090⟩, ⟨(-1749308676643779027), (-1749074835683673011)⟩, true⟩

def words03 : List Nat := [360582001231176046, 360582002902369211, 360582005252594820, 360582007941120548, 360582009946764031, 360582011952383167, 360582013522838315, 360582014732327808, 360582015922667550, 360582017113115424]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360652848707749947, 360652857735874170⟩, ⟨(-2716534885524005356), (-2716300857567927544)⟩, true⟩

def words04 : List Nat := [360582018621878783, 360582019844279253, 360582020725552281, 360582021606836021, 360582022315776788, 360582023644309158, 360582025378413109, 360582027112525495, 360582028508279697, 360582030355686746]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk383A
