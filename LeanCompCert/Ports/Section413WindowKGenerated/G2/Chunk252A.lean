import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk252A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360609693221613468, 360609696983871697⟩, ⟨(-652089365905828298), (-652025229034271980)⟩, true⟩

def state01 : KState := ⟨⟨360515744411862729, 360515748177220661⟩, ⟨1715723724161358890, 1715787939161595274⟩, true⟩

def words00 : List Nat := [360583824583384983, 360583824583714409, 360583823606621005, 360583821735058416, 360583819863590802, 360583817417253278, 360583815759213656, 360583813430306190, 360583811101549848, 360583807992340122]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598314248168671, 360598318016637955⟩, ⟨(-366462159397425760), (-366397865944520962)⟩, true⟩

def words01 : List Nat := [360583805292999602, 360583803101140827, 360583800909357974, 360583799399734242, 360583797938296309, 360583795033260157, 360583792128391578, 360583790364364851, 360583789948652821, 360583790525026024]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360538448706682293, 360538452478293174⟩, ⟨1143164428778988601, 1143228801478740199⟩, true⟩

def words02 : List Nat := [360583790525324792, 360583789889680829, 360583787689969184, 360583785718670539, 360583783747441604, 360583781353463434, 360583777395831652, 360583772660349871, 360583767925174056, 360583764757384682]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360492554241363109, 360492558016078642⟩, ⟨2301478240447490279, 2301542691493248419⟩, true⟩

def words03 : List Nat := [360583762961754817, 360583761890597208, 360583760819489296, 360583758766130361, 360583757219229701, 360583754508791786, 360583751798469194, 360583750654424935, 360583747947648031, 360583744335075998]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586172867908223, 360586176645742206⟩, ⟨(-61792149663657354), (-61727619893140522)⟩, true⟩

def words04 : List Nat := [360583740722716023, 360583738051866813, 360583736747876460, 360583736878799263, 360583736879109295, 360583735314916588, 360583733320581542, 360583732891479231, 360583732462319241, 360583732084342930]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk252A
