import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk801A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571570782853551, 360571612577173063⟩, ⟨843193629587168216, 845454609520948944⟩, true⟩

def state01 : KState := ⟨⟨360573124836325491, 360573166641452719⟩, ⟨718673834985824953, 720935680670266903⟩, true⟩

def words00 : List Nat := [360582167435227301, 360582167300680691, 360582167152061860, 360582166925636174, 360582166699023500, 360582166397718837, 360582166199299421, 360582166156745115, 360582166114059712, 360582165963393429]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 80100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 80100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589100458270807, 360589142274204388⟩, ⟨(-561221665548602367), (-558958954112798005)⟩, true⟩

def words01 : List Nat := [360582165895260374, 360582165939798159, 360582166007948379, 360582166009094534, 360582165987087623, 360582165822956629, 360582165658610437, 360582165662867399, 360582165750875166, 360582165839136019]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 80110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 80100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360577008796180413, 360577050623036545⟩, ⟨407587242739390470, 409850829344417128⟩, true⟩

def words02 : List Nat := [360582165840159758, 360582165852758752, 360582165955589135, 360582166058759793, 360582166119773012, 360582166120918832, 360582166026569238, 360582165834631415, 360582165642495165, 360582165446814711]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 80120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 80100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360561223776272273, 360561265613923660⟩, ⟨1672554560876675844, 1674819012558277952⟩, true⟩

def words03 : List Nat := [360582165444074479, 360582165505390227, 360582165506411311, 360582165489852258, 360582165356827278, 360582165103694543, 360582164850196334, 360582164720436464, 360582164538510717, 360582164278916901]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 80130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 80100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602293920143955, 360602335768628171⟩, ⟨(-1619056902261415190), (-1616791582384449274)⟩, true⟩

def words04 : List Nat := [360582164019069827, 360582163922006184, 360582163922949028, 360582163913929234, 360582163904835821, 360582163757859488, 360582163586912910, 360582163571752536, 360582163695275153, 360582163948159501]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 80140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 80100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk801A
