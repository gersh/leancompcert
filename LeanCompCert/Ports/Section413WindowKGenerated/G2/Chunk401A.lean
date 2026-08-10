import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk401A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360641197682450962, 360641207589190408⟩, ⟨(-2349222890981464164), (-2348954393291447982)⟩, true⟩

def state01 : KState := ⟨⟨360594009729964257, 360594019641884659⟩, ⟨(-457024164362119326), (-456755458890329600)⟩, true⟩

def words00 : List Nat := [360582632784003881, 360582633315138647, 360582633561436939, 360582633807878815, 360582633808335619, 360582633708874517, 360582633518903337, 360582632946498444, 360582632374018805, 360582632355133137]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360546333673891068, 360546343590925459⟩, ⟨1455668319045953400, 1455937229665664842⟩, true⟩

def words01 : List Nat := [360582633259626730, 360582634164180053, 360582634755863893, 360582634983271787, 360582634983726664, 360582634961828522, 360582634939782920, 360582634586198103, 360582634056964795, 360582633152980935]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360610741311293737, 360610751233456221⟩, ⟨(-1128689465606988923), (-1128420349222446611)⟩, true⟩

def words02 : List Nat := [360582632248917642, 360582631765466359, 360582632043726158, 360582632493105764, 360582632493607546, 360582632416115597, 360582631720184662, 360582631644229562, 360582632111308198, 360582632812554115]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590281356437416, 360590291283789075⟩, ⟨(-307527642982738863), (-307258318331729507)⟩, true⟩

def words03 : List Nat := [360582633010244152, 360582633207968427, 360582633828153093, 360582634759448590, 360582635345233121, 360582635931077003, 360582636081381796, 360582636425391542, 360582636616538385, 360582636807858438]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579317044118430, 360579326976589167⟩, ⟨132542333165060411, 132811863321348793⟩, true⟩

def words04 : List Nat := [360582637482947330, 360582637540244597, 360582637540729049, 360582637287516015, 360582637034232862, 360582636254130171, 360582635784604726, 360582635584629753, 360582635384610283, 360582634868577246]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk401A
