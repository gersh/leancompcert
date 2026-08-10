import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk930A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589409669684652, 360589466666466259⟩, ⟨(-695962572152968758), (-692383193696036396)⟩, true⟩

def state01 : KState := ⟨⟨360594684169710657, 360594741179186594⟩, ⟨(-1186472888514782164), (-1182892329423539216)⟩, true⟩

def words00 : List Nat := [360582021962622934, 360582022216409458, 360582022399865881, 360582022583464223, 360582022670641579, 360582022816571434, 360582023001208841, 360582023186097296, 360582023272950199, 360582023411079343]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360615465105043140, 360615522127220477⟩, ⟨(-3119446761974358100), (-3115865021464814830)⟩, true⟩

def words01 : List Nat := [360582023645216119, 360582023879745347, 360582024192186695, 360582024389585255, 360582024485891334, 360582024582313726, 360582024774344420, 360582025043266590, 360582025404460946, 360582025765952970]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591578185967032, 360591635220987859⟩, ⟨(-897482062477802901), (-893899127205452813)⟩, true⟩

def words02 : List Nat := [360582026059410268, 360582026237725632, 360582026385204008, 360582026533076701, 360582026638155317, 360582026651764313, 360582026652971789, 360582026579749830, 360582026506265491, 360582026605287658]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360571121059952681, 360571178107635754⟩, ⟨1005779525443481468, 1009363638750202948⟩, true⟩

def words03 : List Nat := [360582026780131739, 360582026955230531, 360582027072850691, 360582027098296586, 360582027099424905, 360582027062840340, 360582027025880150, 360582026986567610, 360582026929195128, 360582026813985176]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570224026464035, 360570281086856770⟩, ⟨1089221418739033852, 1092806714616957200⟩, true⟩

def words04 : List Nat := [360582026698480417, 360582026561111078, 360582026481003709, 360582026408518936, 360582026335907545, 360582026165128555, 360582025878884253, 360582025708463595, 360582025537658592, 360582025382553890]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk930A
